import sys
import os

try:
    import tomllib
except ImportError:
    import tomli as tomllib

class CodeGenerator:
    def __init__(self, type_checker_template, type_checker_template_output, input_command):
        self.typerules             = ""
        self.pre_typerules         = ""
        self.const_rules           = ""
        self.type_checker_includes = ""
        self.template_data         = ""
        self.input_command         = input_command
        self.copyright             = "2010-2022"
        
        self.copyright_replacement_pattern          = b'${copyright}'
        self.generation_command_replacement_pattern = b'${generation_command}'
        self.template_file_path_replacement_pattern = b'${template_file_path}'
        self.typerules_replacement_pattern          = b'${typerules}'
        self.pre_typerules_replacement_pattern      = b'${pretyperules}'
        self.const_rules_replacement_pattern        = b'${construles}'
        self.typechecker_header_replacement_pattern = b'${typechecker_includes}'
        
        self.type_checker_template        = type_checker_template
        self.type_checker_template_output = type_checker_template_output
        
    
    def read_template_data(self):
        with open(self.type_checker_template, "rb") as f:
            self.template_data = f.read()
    
    def generate_file_header(self):
        self.fill_template(self.copyright_replacement_pattern, self.copyright)
        self.fill_template(self.generation_command_replacement_pattern, self.input_command)
        self.fill_template(self.template_file_path_replacement_pattern, self.type_checker_template )

    def generate_code_for_typerules(self, input_typerules):
        for input_typerule in input_typerules:
            input_typerule_name = input_typerule["name"]
            input_typerule_type_checker_class = input_typerule["type_checker_class"]

            self.typerules = f"""{self.typerules}
    case Kind::{input_typerule_name}:
        typeNode = {input_typerule_type_checker_class}::computeType(nodeManager, n, check, errOut);
        break;
            """
            
            self.pre_typerules = f"""{self.pre_typerules}
    case Kind::{input_typerule["name"]}:
        typeNode = {input_typerule["type_checker_class"]}::preComputeType(nodeManager, n);
        break;
            """

    def generate_code_for_type_checker_includes(self, type_checker_include):
        self.type_checker_includes = f"""{self.type_checker_includes}\n#include \"{type_checker_include}\""""
    
    def generate_code_for_const_rules(self, const_rules):
        for input_const_rule in const_rules:
            input_const_rule_name = input_const_rule["name"]
            input_const_rule_checker_class = input_const_rule["type_checker_class"]

            self.const_rules = f"""{self.const_rules}
    case Kind::{input_const_rule_name}:
        return {input_const_rule_checker_class}::computeIsConst(nodeManager, n);
            """

    def fill_type_checker_includes_template_data(self):
        self.fill_template(self.typechecker_header_replacement_pattern, self.type_checker_includes)

    def fill_typerules_template_data(self):
        self.fill_template(self.typerules_replacement_pattern, self.typerules)
        self.fill_template(self.pre_typerules_replacement_pattern, self.pre_typerules)

    def fill_const_rules_template_data(self):
        self.fill_template(self.const_rules_replacement_pattern, self.const_rules)
    
    def fill_template(self, target_pattern, replacement_string):
        self.template_data = self.template_data.replace(target_pattern, str.encode(replacement_string))
    
    def write_output_data(self):
        with open(self.type_checker_template_output, 'wb') as f:
            f.write(self.template_data)

class TheoryValidator:
    def __init__(self):
        self.seen_theory_builtin = False
    
    def validateTheory(self, filename, kinds):
        theory = kinds.get("theory")

        if not theory:
            print(f"{filename}: error: theory not defined")
            exit(1)

        theory_id = theory.get("id")
        theory_class = theory.get("base_class")
        theory_header = theory.get("base_class_header")

        if not theory_id:
            print(f"{filename}: error: theory id not defined")
            exit(1)
        
        if theory_id == 'THEORY_BUILTIN':
            if self.seen_theory_builtin:
                print(f"{filename}: error: \"builtin\" theory redefined")
                exit(1)
            self.seen_theory_builtin = True
        
        if not theory_class or not theory_header:
            print(f"{filename}: error: \"theory\" directive missing class or header argument")
            exit(1)

        if not theory_class.startswith("::"):
            print(f"{filename}: warning: theory class `{theory_class}` isn't fully-qualified (e.g., ::cvc5::internal::theory::foo)")
        
        if not theory_class.startswith("::cvc5::internal::theory::"):
            print(f"{filename}: warning: theory class not under ::cvc5::internal::theory namespace")

def mkexpr_main():
    type_checker_template = sys.argv[1]
    type_checker_template_output = sys.argv[2]
    kinds_input_files = sys.argv[3:]
    input_command = ' '.join(sys.argv)
    
    cg = CodeGenerator(type_checker_template, type_checker_template_output, input_command)
    cg.read_template_data()
    cg.generate_file_header()

    tv = TheoryValidator()

    # Check if given kinds files exist.
    for file in kinds_input_files:
        if not os.path.exists(file):
            exit(f"Kinds file '{file}' does not exist")

    # Parse and check toml files
    for filename in kinds_input_files:
        try:
            with open(filename, "rb") as f:
                kinds_data = tomllib.load(f)
                
                tv.validateTheory(filename, kinds_data)

                typerules_input = kinds_data.get("typerules", [])
                cg.generate_code_for_typerules(typerules_input)
                
                type_checker_include = kinds_data["theory"]["typechecker_header"]
                cg.generate_code_for_type_checker_includes(type_checker_include)
                
                const_rules = kinds_data.get("construles", [])
                cg.generate_code_for_const_rules(const_rules)
        except Exception as e:
            print(f"Could not parse file {filename}")
            print(e)
            exit(1)

    cg.fill_typerules_template_data()
    cg.fill_type_checker_includes_template_data()
    cg.fill_const_rules_template_data()
    cg.write_output_data()

if __name__ == "__main__":
    mkexpr_main()
    exit(0)