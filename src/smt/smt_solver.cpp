/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The solver for SMT queries in an SolverEngine.
 */

#include "smt/smt_solver.h"

#include "options/base_options.h"
#include "options/main_options.h"
#include "options/smt_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "prop/prop_engine.h"
#include "smt/assertions.h"
#include "smt/env.h"
#include "smt/logic_exception.h"
#include "smt/preprocessor.h"
#include "smt/solver_engine_stats.h"
#include "theory/logic_info.h"
#include "theory/theory_engine.h"
#include "theory/theory_traits.h"

using namespace std;

namespace cvc5::internal {
namespace smt {

SmtSolver::SmtSolver(Env& env, SolverEngineStatistics& stats)
    : EnvObj(env),
      d_pp(env, stats),
      d_asserts(env),
      d_stats(stats),
      d_theoryEngine(nullptr),
      d_propEngine(nullptr),
      d_ppAssertions(userContext()),
      d_ppSkolemMap(userContext())
{
}

SmtSolver::~SmtSolver() {}

void SmtSolver::finishInit()
{
  Trace("limit") << "cvc5::internal::SmtSolver finishInit" << std::endl;
  // We have mutual dependency here, so we add the prop engine to the theory
  // engine later (it is non-essential there)
  d_theoryEngine.reset(new TheoryEngine(d_env));

  // Add the theories
  for (theory::TheoryId id = theory::THEORY_FIRST; id < theory::THEORY_LAST;
       ++id)
  {
    theory::TheoryConstructor::addTheory(d_theoryEngine.get(), id);
  }
  // Add the proof checkers for each theory
  ProofNodeManager* pnm = d_env.getProofNodeManager();
  if (pnm)
  {
    // reset the rule checkers
    pnm->getChecker()->reset();
    // add rule checkers from the theory engine
    d_theoryEngine->initializeProofChecker(pnm->getChecker());
  }
  Trace("smt-debug") << "Making prop engine..." << std::endl;
  /* force destruction of referenced PropEngine to enforce that statistics
   * are unregistered by the obsolete PropEngine object before registered
   * again by the new PropEngine object */
  d_propEngine.reset(nullptr);
  d_propEngine.reset(new prop::PropEngine(d_env, d_theoryEngine.get()));

  Trace("smt-debug") << "Setting up theory engine..." << std::endl;
  d_theoryEngine->setPropEngine(getPropEngine());
  Trace("smt-debug") << "Finishing init for theory engine..." << std::endl;
  d_theoryEngine->finishInit();
  d_propEngine->finishInit();
  d_pp.finishInit(d_theoryEngine.get(), d_propEngine.get());
}

void SmtSolver::resetAssertions()
{
  Trace("limit") << "cvc5::internal::SmtSolver resetAssertions" << std::endl;
  /* Create new PropEngine.
   * First force destruction of referenced PropEngine to enforce that
   * statistics are unregistered by the obsolete PropEngine object before
   * registered again by the new PropEngine object */
  d_propEngine.reset(nullptr);
  d_propEngine.reset(new prop::PropEngine(d_env, d_theoryEngine.get()));
  d_theoryEngine->setPropEngine(getPropEngine());
  // Notice that we do not reset TheoryEngine, nor does it require calling
  // finishInit again. In particular, TheoryEngine::finishInit does not
  // depend on knowing the associated PropEngine.
  d_propEngine->finishInit();
  // must reset the preprocessor as well
  d_pp.finishInit(d_theoryEngine.get(), d_propEngine.get());
}

void SmtSolver::interrupt()
{
  Trace("limit") << "cvc5::internal::SmtSolver interrupt" << std::endl;
  if (d_propEngine != nullptr)
  {
    Trace("limit") << "cvc5::internal::SmtSolver d_propEngine interrupt" << std::endl;
    d_propEngine->interrupt();
  }
  if (d_theoryEngine != nullptr)
  {
    Trace("limit") << "cvc5::internal::SmtSolver d_theoryEngine interrupt" << std::endl;
    d_theoryEngine->interrupt();
  }
}

Result SmtSolver::checkSatInternal()
{
  Trace("limit") << "cvc5::internal::SmtSolver checkSatInternal" << std::endl;
  // call the prop engine to check sat
  return d_propEngine->checkSat();
}

void SmtSolver::preprocess(preprocessing::AssertionPipeline& ap)
{
  Trace("limit") << "cvc5::internal::SmtSolver preprocess" << std::endl;

  ResourceManager* rm = d_env.getResourceManager();

  if (rm->outOfTime())
  {
    Trace("limit") << "cvc5::internal::SmtSolver out of time preprocess" << std::endl;
    return;
  }
  if (rm->outOfResources())
  {
    Trace("limit") << "cvc5::internal::SmtSolver out of resources preprocess" << std::endl;
    return;
  }

  TimerStat::CodeTimer paTimer(d_stats.d_processAssertionsTime);
  d_env.getResourceManager()->spendResource(Resource::PreprocessStep);

  // process the assertions with the preprocessor
  d_pp.process(ap);

  // end: INVARIANT to maintain: no reordering of assertions or
  // introducing new ones
}

void SmtSolver::assertToInternal(preprocessing::AssertionPipeline& ap)
{
  Trace("limit") << "cvc5::internal::SmtSolver assertToInternal" << std::endl;
  // get the assertions
  const std::vector<Node>& assertions = ap.ref();
  preprocessing::IteSkolemMap& ism = ap.getIteSkolemMap();
  // assert to prop engine, which will convert to CNF
  d_env.verbose(2) << "converting to CNF..." << endl;
  d_propEngine->assertInputFormulas(assertions, ism);

  // It is important to distinguish the input assertions from the skolem
  // definitions, as the decision justification heuristic treates the latter
  // specially. Note that we don't pass the preprocess learned literals
  // d_pp.getLearnedLiterals() here, since they may not exactly correspond
  // to the actual preprocessed learned literals, as the input may have
  // undergone further preprocessing.
  // if we can deep restart, we always remember the preprocessed formulas,
  // which are the basis for the next check-sat.
  if (trackPreprocessedAssertions())
  {
    // incompatible with global negation
    Assert(!options().quantifiers.globalNegate);
    theory::SubstitutionMap& sm = d_env.getTopLevelSubstitutions().get();
    size_t startIndex = d_ppAssertions.size();
    // remember the assertions and Skolem mapping
    for (const Node& a : assertions)
    {
      d_ppAssertions.push_back(a);
    }
    for (const std::pair<const size_t, Node>& k : ism)
    {
      // optimization: skip skolems that were eliminated in preprocessing
      if (sm.hasSubstitution(k.second))
      {
        continue;
      }
      size_t newIndex = k.first + startIndex;
      d_ppSkolemMap[newIndex] = k.second;
    }
  }
}

const context::CDList<Node>& SmtSolver::getPreprocessedAssertions() const
{
  Trace("limit") << "cvc5::internal::SmtSolver getPreprocessedAssertions" << std::endl;
  return d_ppAssertions;
}

const context::CDHashMap<size_t, Node>& SmtSolver::getPreprocessedSkolemMap()
    const
{
  Trace("limit") << "cvc5::internal::SmtSolver getPreprocessedSkolemMap" << std::endl;
  return d_ppSkolemMap;
}

bool SmtSolver::trackPreprocessedAssertions() const
{
  Trace("limit") << "cvc5::internal::SmtSolver trackPreprocessedAssertions" << std::endl;
  return options().smt.deepRestartMode != options::DeepRestartMode::NONE
         || options().smt.produceProofs;
}

TheoryEngine* SmtSolver::getTheoryEngine() { 
  Trace("limit") << "cvc5::internal::SmtSolver getTheoryEngine" << std::endl;
  return d_theoryEngine.get(); 
  }

prop::PropEngine* SmtSolver::getPropEngine() { 
  Trace("limit") << "cvc5::internal::SmtSolver getPropEngine" << std::endl;
  return d_propEngine.get(); 
  }

theory::QuantifiersEngine* SmtSolver::getQuantifiersEngine()
{
  Trace("limit") << "cvc5::internal::SmtSolver getQuantifiersEngine" << std::endl;
  Assert(d_theoryEngine != nullptr);
  return d_theoryEngine->getQuantifiersEngine();
}

Preprocessor* SmtSolver::getPreprocessor() { 
  Trace("limit") << "cvc5::internal::SmtSolver getPreprocessor" << std::endl;
  return &d_pp; 
  }

Assertions& SmtSolver::getAssertions() { 
  Trace("limit") << "cvc5::internal::SmtSolver getAssertions" << std::endl;
  return d_asserts; 
  }

void SmtSolver::pushPropContext()
{
  Trace("limit") << "cvc5::internal::SmtSolver pushPropContext" << std::endl;
  TimerStat::CodeTimer pushPopTimer(d_stats.d_pushPopTime);
  Assert(d_propEngine != nullptr);
  d_propEngine->push();
}

void SmtSolver::popPropContext()
{
  Trace("limit") << "cvc5::internal::SmtSolver popPropContext" << std::endl;
  TimerStat::CodeTimer pushPopTimer(d_stats.d_pushPopTime);
  Assert(d_propEngine != nullptr);
  d_propEngine->pop();
}

void SmtSolver::resetTrail()
{
  Trace("limit") << "cvc5::internal::SmtSolver resetTrail" << std::endl;
  Assert(d_propEngine != nullptr);
  d_propEngine->resetTrail();
}

}  // namespace smt
}  // namespace cvc5::internal
