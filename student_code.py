import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_retract(self, fact_or_rule):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact_or_rule])
        ####################################################
        # Student code goes here
        #If the fact_or_rule input is a Rule, output an error.
        if isinstance(fact_or_rule, Rule):
            print("Rules cannot be retracted. Please input fact to be retracted.")
            return
        #If the fact_or_rule input is a Fact, proceed
        elif isinstance(fact_or_rule, Fact):
            #If the fact is in the KB, proceed
            if fact_or_rule in self.facts:
                #Get the actual fact in the KB and store it.
                actual_fact = self._get_fact(fact_or_rule)
                #Send to fact handler to handle different scenarios a fact may encounter
                self.fact_handler(actual_fact)
            #If the factis in the KB, output an error
            else:
                print("Fact is not in the KB, so it cannot be retracted.")
                return
        #If the fact_or_rule input is neither a fact nor a rule, output an error.
        else:
            print("Input is neither fact nor rule. Please input fact to be retracted.")
            return

    def fact_handler(self, fact):
        """Handle facts encountered in kb_retract

        Args:
            fact (Fact) - Fact to be handled

        Returns:
            None
        """        

        #Get the actual fact in the KB and store it.
        actual_fact = self._get_fact(fact)
        #If the fact is supported by other facts or rules, proceed.
        if fact.supported_by:
            #If the fact is asserted, toggle fact.asserted and no no more.
            if fact.asserted:
                fact.asserted = False
                print("Fact is no longer asserted, but it still exists in KB since other rules or facts support it.")
                return
            #If the fact is not asserted, do nothing
            else:
                print("Fact was supported by other rules or facts but not asserted, so it was not retracted from KB.")
        #If the fact is not supported by some other facts or rules then it MUST BE ASSERTED, proceed.
        else:  
            #Store the facts supported by the fact being retracted in supported_facts
            supported_facts = fact.supports_facts
            #Iterate through all the supported facts in supported_facts
            for supported_fact in supported_facts:
                #Checks if supported facts need to be removed as well.
                self.supported_fact_handler_fact_variant(supported_fact, fact)
            #Store the facts supported by the fact being retracted in supported_facts
            supported_rules = fact.supports_rules
            #Iterate through all the supported facts in supported_facts
            for supported_rule in supported_rules:
                #Checks if supported rules need to be removed as well
                self.supported_rule_handler_fact_variant(supported_rule, fact)
            #Remove the fact from the KB
            self.facts.remove(actual_fact)
            print("Fact has been retracted along with all facts and rules that the fact was solely supporting.")
            return

    def rule_handler(self, rule):
        """Handle rules encountered in kb_retract

        Args:
            rule (Rule) - Rule to be handled

        Returns:
            None
        """   
        #Get the actual fact in the KB and store it.
        real_rule = self._get_rule(rule)
        #If the rule is supported by other facts or rules, proceed.
        if rule.supported_by:
            #If the rule is asserted, do nothing
            if rule.asserted:
                print("Rule is asserted, so it cannot be retracted")
                return
            #If the rule is not asserted, do nothing
            else:
                print("Rule is supported by other facts and/or rules, so it cannot be retracted.")
        #If the rule is not supported by some other facts or rules then it MUST BE ASSERTED, proceed.
        else:  
            #Store the facts supported by the rule being retracted in supported_facts
            supported_facts = rule.supports_facts
            #Iterate through all the supported facts in supported_facts
            for supported_fact in supported_facts:
                #Checks if supported facts need to be removed as well.
                self.supported_fact_handler_rule_variant(supported_fact, rule)
            #Store the facts supported by the rule being retracted in supported_facts
            supported_rules = rule.supports_rules
            #Iterate through all the supported facts in supported_facts
            for supported_rule in supported_rules:
                #Checks if supported rules need to be removed as well
                self.supported_rule_handler_rule_variant(supported_rule, rule)
            #Remove the fact from the KB
            self.rules.remove(real_rule)
            print("Fact has been retracted along with all facts and rules that the fact was solely supporting.")
            return


    def supported_fact_handler_fact_variant(self, supported_fact, fact):
        """Handle facts and rules that the fact being removed supported

        Args:
            supported_fact (Fact) - Inferred Fact to be retracted
            fact (Fact) - Fact to be handled


        Returns:
            None
        """

        #Store the actual supported fact from the KB
        real_supported_fact = self._get_fact(supported_fact)
        #Store the bindings that support the supported fact in supporting_bindings
        supporting_bindings = real_supported_fact.supported_by
        #Iterates through each supporting binding 
        for binding in supporting_bindings:
            #Check if the fact being retracted is in a binding
            if fact in binding:
                #Remove binding from supported fact
                real_supported_fact.supported_by.remove(binding)
                #Remove fact from binding
                binding.remove(fact)




        #Check if the supported fact is no longer supported 
        if not real_supported_fact.supported_by:
            self.fact_handler(real_supported_fact)



    def supported_rule_handler_fact_variant(self, supported_rule, fact):
        """Handle rules that the fact being removed supported

        Args:
            rule (Rule) - Inferred Rule to be retracted
            fact (Fact) - Fact to be handled

        Returns:
            None
        """       

        #Store the actual supported rule from the KB
        real_supported_rule = self._get_rule(supported_rule)
        #Store the bindings that support the supported rule in supporting_bindings
        supporting_bindings = real_supported_rule.supported_by
        #Iterates through each supporting binding 
        for binding in supporting_bindings:
            #Check if the fact being retracted is in a binding
            if fact in binding:
                #Remove binding from supported fact
                real_supported_rule.supported_by.remove(binding)
                #Remove fact from binding                
                binding.remove(fact)



        #Check if the supported fact is no longer supported 
        if not real_supported_rule.supported_by:
            self.rule_handler(real_supported_rule)

    def supported_fact_handler_rule_variant(self, supported_fact, rule):
        """Handle facts that the rule being removed supported

        Args:
            supported_fact (Fact) - Inferred Fact to be retracted
            fact (Fact) - Fact to be handled


        Returns:
            None
        """

        #Store the actual supported fact from the KB
        real_supported_fact = self._get_fact(supported_fact)
        #Store the bindings that support the supported fact in supporting_bindings
        supporting_bindings = real_supported_fact.supported_by
        #Iterates through each supporting binding 
        for binding in supporting_bindings:
            #Check if the fact being retracted is in a binding
            if rule in binding:
                #Remove binding from supported fact
                real_supported_fact.supported_by.remove(binding)
                #Remove fact from binding
                binding.remove(rule)


        #Check if the supported fact is no longer supported 
        if not real_supported_fact.supported_by:
            self.fact_handler(real_supported_fact)



    def supported_rule_handler_rule_variant(self, supported_rule, rule):
        """Handle rules that the rule being removed supported

        Args:
            rule (Rule) - Inferred Rule to be retracted
            fact (Fact) - Fact to be handled

        Returns:
            None
        """       

        #Store the actual supported rule from the KB
        real_supported_rule = self._get_rule(supported_rule)
        #Store the bindings that support the supported rule in supporting_bindings
        supporting_bindings = real_supported_rule.supported_by
        #Iterates through each supporting binding 
        for binding in supporting_bindings:
            #Check if the fact being retracted is in a binding
            if rule in binding:
                #Remove binding from supported fact
                real_supported_rule.supported_by.remove(binding)
                #Remove fact from binding                
                binding.remove(rule)



        #Check if the supported fact is no longer supported 
        if not real_supported_rule.supported_by:
            self.rule_handler(real_supported_rule)

        

class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing            
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Student code goes here

        #If the first rule on the left hand side of the rule matches with the fact's statement, proceed.
        if match(rule.lhs[0], fact.statement):
            #If the left hand side of the rule contains more than one statement, proceed
            if (len(rule.lhs) > 1):
                #Create a list for the inferred rule's lhs's statements
                inferred_lhs_statements = []
                #Cycle through the lhs of the rule 
                for rule_statement in rule.lhs[1:]:
                    #Instantiate a new statement inference created from a lhs statement of the rule and 
                    #the binding created from matching the fact's statement 
                    inferred_lhs_statement = instantiate(rule_statement, match(rule.lhs[0], fact.statement))
                    #Add the new statement to the temporary list.
                    inferred_lhs_statements.append(inferred_lhs_statement)
                #Instantiate a new statement inference created from the right hand side of the rule and 
                #the binding created from matching the fact's statement and the first left hand side's rule.
                inferred_rhs_statement = instantiate(rule.rhs, match(rule.lhs[0], fact.statement))
                #Create a new inferred rule that is supported by the rule and fact pair passed into fc_infer
                inferred_rule = Rule([inferred_lhs_statements, inferred_rhs_statement], [[fact, rule]])
                #Add the inferred rule to the knowledge base's fact's supported_facts list
                fact.supports_rules.append(inferred_rule)
                #Add the inferred rule to the knowledge base's rule's supported_facts list
                rule.supports_rules.append(inferred_rule)
                #Add the inferred rule into the knowledge base
                kb.kb_assert(inferred_rule)

            #If the left hand side of the rule contains only one statement, proceed
            elif (len(rule.lhs) == 1):
                #Instantiate a new statement inference created from the right hand side of the rule and 
                #the binding created from matching the fact's statement and the first left hand side's rule.
                inferred_statement = instantiate(rule.rhs, match(rule.lhs[0], fact.statement))
                #Create a new inferred fact that is supported by the rule and fact pair passed into fc_infer
                inferred_fact = Fact(inferred_statement, [[rule, fact]])
                #Add the inferred fact to the knowledge base's fact's supported_facts list
                fact.supports_facts.append(inferred_fact)
                #Add the inferred fact to the knowledge base's rule's supported_facts list
                rule.supports_facts.append(inferred_fact)
                #Add the inferred fact into the knowledge base
                kb.kb_assert(inferred_fact)

            #If the left hand side of a rule contains less than one statement, print error
            else:
                print("Rule with no LHS in KB.")

