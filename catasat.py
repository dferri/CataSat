import argparse
import re
import z3

# S-expression parser

term_regex = r'''(?mx)
    \s*(?:
        (?P<brackl>\()|
        (?P<brackr>\))|
        (?P<num>\-?\d+\.\d+|\-?\d+)|
        (?P<sq>"[^"]*")|
        (?P<s>[^(^)\s]+)
       )'''


def parse_sexp(sexp):
    stack = []
    out = []
    for termtypes in re.finditer(term_regex, sexp):
        term, value = [(t,v) for t,v in termtypes.groupdict().items() if v][0]
        if   term == 'brackl':
            stack.append(out)
            out = []
        elif term == 'brackr':
            assert stack, "Trouble with nesting of brackets"
            tmpout, out = out, stack.pop(-1)
            out.append(tmpout)
        elif term == 'num':
            v = float(value)
            if v.is_integer(): v = int(v)
            out.append(v)
        elif term == 'sq':
            out.append(value[1:-1])
        elif term == 's':
            out.append(value)
        else:
            raise NotImplementedError("Error: %r" % (term, value))
    assert not stack, "Trouble with nesting of brackets"
    return out[0]


def print_sexp(exp):
    out = ''
    if type(exp) == type([]):
        out += '(' + ' '.join(print_sexp(x) for x in exp) + ')'
    elif type(exp) == type('') and re.search(r'[\s()]', exp):
        out += '"%s"' % repr(exp)[1:-1].replace('"', '\"')
    else:
        out += '%s' % exp
    return out


def checkSat(script):
    """Check if `script` is sat, where `script` is a list of parsed s-expressions
    """
    res = "\n".join([print_sexp(sexp) for sexp in script])

    solver = z3.Solver()
    solver.reset()
    constraints = z3.parse_smt2_string(res)
    solver.add(constraints)
    return solver.check(), solver


class Catamorphism(object):
    def __init__(self, name, definition, input_type, return_type,
                 range_constraint=None):
        self.name = name
        self.definition = definition
        self.input_type = input_type
        self.return_type = return_type

        # A range constraint is a tuple of the form:
        # (r: str, f: s-exp) where `r` is a variable and `f` is a formula
        # specifying the range constraint
        self.range_constraint = range_constraint

        # Dictionary of the definition of the value of catamorphism
        # on a single constructor
        # i.e. defByCon[constructor] = (vars, def)
        self.defByCon = {}

        # `definition[4][2]` is a `<match_case>`
        for matchCase in definition[4][2]:
            """
            <match_case>  ::=  ( <pattern> <term> )
            <pattern>     ::=  <symbol> | ( <symbol> <symbol>+ )
            """
            term = matchCase[1]
            if type(matchCase[0]) == str:
                # Find the Constructor for that match_case
                conName = matchCase[0]
                con = [c for c in self.input_type.constructors
                       if c.name == conName][0]
                self.defByCon[con] = ([], term)
            elif type(matchCase[0]) == list:
                conName = matchCase[0][0]
                con = [c for c in self.input_type.constructors
                       if c.name == conName][0]
                self.defByCon[con] = (matchCase[0][1:], term)
            else:
                raise Exception("Wrong catamorphism definition: {}"
                                .format(definition))

    def __repr__(self):
        return ("{}: {} → {}\n".format(
            self.name, self.input_type.name, self.return_type))


def subInSexp(sexp, x, y):
    """Substitute (replace) `x` with `y` in `sexp`, i.e. returns `sexp[y/x]`
    """
    if type(sexp) != list:
        return (y if sexp == x else sexp)
    else:
        return [subInSexp(s, x, y) for s in sexp]


def subListInSexp(sexp, xys):
    """Given a list of tuples of the form xys = [(x1, y1), ..., (xn, yn)]
    substitute (replace) `x` with `y` in `sexp`
    i.e. returns `sexp[y1/x1, ..., yn/xn]`
    """
    d = dict(xys)

    if type(sexp) != list:
        return (d[sexp] if sexp in d else sexp)
    else:
        return [subListInSexp(s, xys) for s in sexp]


class Selector(object):
    """ <selector_dec> ::= (<symbol> <sort>) """
    def __init__(self, name, index, return_type, constructor, datatype):
        self.name = name
        self.index = index
        self.return_type = return_type
        self.constructor = constructor
        self.datatype = datatype

    def __repr__(self):
        return ("({} {})".format(self.name, self.datatype.name))

    def __str__(self):
        return ("({} {})".format(self.name, self.datatype.name))


class Constructor(object):
    """
    <constructor_dec> ::= (<symbol> <selector_dec>∗)
    <selector_dec> ::= (<symbol> <sort>)
    E.g.:
        (empty)
        (cons (head Int) (tail IntList))))
    """
    def __init__(self, name, selSexps, datatype):
        self.name = name
        self.datatype = datatype

        self.selectors = []
        for i, sel in enumerate(selSexps):
            assert(len(sel) == 2)
            self.selectors.append(Selector(sel[0], i, sel[1],
                                           self, self.datatype))

    def __repr__(self):
        return ("({} ({}))".format(self.name, self.selectors))

    def __str__(self):
        res = "(" + self.name
        for sel in self.selectors:
            res = res + "\n    ({})".format(sel)
        return res + ")"

    def isNullary(self):
        return self.selectors == []

class Datatype(object):
    """
    An object representing a datatype. The SMT-LIB syntax is:
        (declare-datatype <symbol> <datatype_dec>)

        <datatype_dec> ::=
            (<constructor_dec>+) | (par (<symbol>+) (<constructor_dec>+))

    Actually we didn't implement parametric sorts yet, so:
        <datatype_dec> ::= <constructor_dec>+
        <constructor_dec> ::= (<symbol> <selector_dec>∗)
        <selector_dec> ::= (<symbol> <sort>)

    E.g.:
        (declare-datatype Color ((red) (green) (blue)))
        (declare-datatype IntList (
            (empty)
            (cons (head Int) (tail IntList))))
    """
    def __init__(self, name, constructors):
        """(declare-datatype <symbol> <datatype_dec>)"""
        self.name = name
        # TODO: order of constructors is important? Maybe use a set
        self.constructors = []

        for c in constructors:
            self.constructors.append(Constructor(c[0], c[1:], self))

    def __repr__(self):
        # res = "(" + self.name
        # for con in self.constructors:
        #     res = res + "\n        ({}".format(con.name)
        #     for sel in con.selectors:
        #         res = res + "\n            {}".format(sel)
        #     res = res + ")"
        # return res + ")\n"
        return(self.name)


class RangeConstraints(object):
    """An object that contains all the range constraints of the catamorphisms
    (it mimics a dictionary)
    """
    def __init__(self):
        # A set of tuples `(catas, range_constraint)` where:
        # - `catas` is a set of catamorphisms
        # - `range_constraint` is the relative collective range constraint
        # (it mimics a dictionary)
        self.constraints = {}

    def addFromSExp(self, sexp, catas):
        """Adds a new range constraint
        (assuming the catamorphisms are already defined in `catas`)
        """
        self.constraints[frozenset({catas[c] for (_, c) in sexp[1]})] = sexp[1:]

    def getFromSet(self, catas):
        """Finds the collective range constraints for the set of catamorphisms `catas`
        """
        return [self.constraints[s]
                for s in self.constraints if s <= catas]

    def __repr__(self):
        return self.constraints.__repr__()
        # return ("{}: {} → {}\n".format(
        #     self.name, self.input_type.name, self.return_type))

def parseCatas(parsed):
    """Substitute the catamorphisms definitions with uninterpreted functions
    (so the file can be handled by Z3) and also returns a list of all the
    catamorphisms, datatypes and range constraints
    """
    datatypes = {}
    # Find datatypes
    for sexp in parsed:
        if sexp[0] == "declare-datatype":
            assert(len(sexp) == 3)
            datatypes[sexp[1]] = Datatype(sexp[1], sexp[2])

    # Find catamorphisms and replace them with uninterpreted functions ("declare-fun")
    res = []
    allCatas = {}
    rangeConstr = RangeConstraints()
    for sexp in parsed:
        if sexp[0] == "define-cata":
            # Replace the catamorphism with a function symbol
            name = sexp[1]
            assert(len(sexp[2]) == 1 and len(sexp[2][0]) == 2)
            input_type = datatypes[sexp[2][0][1]]

            return_type = sexp[3]

            allCatas[name] = Catamorphism(name, sexp, input_type, return_type)
            res.append(["declare-fun", name, [input_type.name], return_type])
        elif sexp[0] == "define-range":
            rangeConstr.addFromSExp(sexp, allCatas)
        else:
            res.append(sexp)

    return res, allCatas, datatypes, rangeConstr


# def listToSet(x):
#     """Flattens an indefinitely nested list of lists into a set of `tokens`"""
#     if type(x) != list:
#         return x
#     else:
#         res = set()
#         for y in x:
#             z = listToSet(y)
#             if type(z) == set:
#                 res = res | z
#             else:
#                 res.add(z)
#         return res


# def findVarsOfList(sexp, varSet):
#     """Finds which variables in the given a set are in the given expression"""
#     tokenSet = listToSet(sexp)
#     tokenSet & varSet


# def findInitialFrontiers(parsed, catas):
#     """Finds all variables in the `parsed` script of all the input types of the
#     catamorphisms in `catas`"""

#     # Variables of types that are input types of catamorphisms
#     cataVarTypes = {}
#     # Names of catamorphisms
#     cataNames = set()
#     for k in catas:
#         cataVarTypes[catas[k].input_type] = set()
#         cataNames.add(k)

#     cataVars = {}
#     for kt in cataVarTypes:
#         cataVars[kt] = set()

#     for sexp in parsed:
#         # Finds "variables" declarations, which are actually constants so:
#         # (declare-fun <symbol> () <sort>)
#         if (sexp[0] == "declare-fun"
#             and sexp[2] == []
#             and sexp[3] in cataVarTypes):
#             cataVars[sexp[3]].add(sexp[1])

#     return cataVars


def findCatamorphismsArguments(sexp, allCatas):
    """Finds all terms that occur as arguments of catamorphisms
    returns a set of terms and their relative catamorphism
    i.e. { (t, c) | c(t) is in the assertions }
    TODO: a list, not a set
    """

    res = []
    if type(sexp) == list:
        if type(sexp[0]) != list and sexp[0] in allCatas:
            tmp = (sexp[1], allCatas[sexp[0]])
            res.append(tmp)
        else:
            for s in sexp:
                res.extend(findCatamorphismsArguments(s, allCatas))

    return res


def createNewVarName(varType):
    """An helper function that returns a new name for creating fresh variables.
    """
    createNewVarName.counter += 1
    # return "v_{}_{}".format(varType.lower(), createNewVarName.counter)
    return "v_{}".format(createNewVarName.counter)


def printSexp(script):
    """Print s-expressions in a more readable way.
    """
    if script:
        print("\n".join([print_sexp(sexp) for sexp in script]))
    else:
        print("()")


def unrollTermCatas(term, catas, allCatas):
    """Unroll all the `catas` applied to `term`
    """
    # The declarations of the fresh variables introduced by the unrolling
    # ( declare-fun <symbol> ( <sort>∗ ) <sort> )
    newVariablesDefinitions = []

    # The fresh variables introduced by the unrolling that need to be added
    # to the frontier
    newVarsFrontier = []

    # The unrolling of the formula
    # \or { for C constructor of sort of `term`}
    #     \land term = C(x1, ..., xn)
    #     \land { for cata in catas }
    #         cata(term) = V(x1, ..., xn)
    unroll = ["or"]

    sort = list(catas)[0].input_type

    for con in sort.constructors:
        if con.isNullary():
            tmp = ["and", ["=", term, con.name]]
            for cata in catas:
                val = cata.defByCon[con][1]
                tmp.append(
                    ["=", [cata.name, term], val]
                )
            unroll.append(tmp)
        else:
            # Create the fresh variables
            newVars = [(createNewVarName(sel.return_type), sel.return_type)
                       for sel in con.selectors]
            newVarsNames = [v for (v, _) in newVars]

            for (vName, vSort) in newVars:
                """
                ( declare-const <symbol> <sort> )
                """
                newVariablesDefinitions.append(
                    ['declare-const', vName, vSort]
                )

            tmp = ["and", ["=", term, [con.name] + newVarsNames]]
            for cata in catas:
                (defVars, defCon) = cata.defByCon[con]
                val = subListInSexp(defCon, list(zip(defVars, newVarsNames)))
                tmp.append(
                    ["=", [cata.name, term], val]
                )

                # Add the variables (that are arguments of some catamorphism)
                # to the frontier
                newVarsFrontier.extend(findCatamorphismsArguments(val, allCatas))

            unroll.append(tmp)
    return (newVariablesDefinitions, newVarsFrontier, unroll)


def print_model(model, parsed):
    """Pretty prints the assignments in the model of the variables defined by the user
    """
    # User define declarations
    usrDecls = [s[1] for s in parsed if s[0] == "declare-const"
                                        or (s[0] == "declare-fun" and s[2] == [])]

    # References to those declaration in the model
    declRefs = []
    # Print only the user defined declarations
    for decl in model.decls():
        if decl.name() in usrDecls:
            declRefs.append(decl)

    for decl in sorted(declRefs, key=lambda d: d.name()):
        print("{} = {}".format(decl.name(), model[decl]))


def groupFrontier(tmpFrontier):
    """Group all the catamorphisms in the frontier by the term they're applied to
    """
    # TODO: switch to tuples instead of lists for s-expressions?
    uniqTerms = []
    for (t, _) in tmpFrontier:
        if not (t in uniqTerms):
            uniqTerms.append(t)
    return [(term, frozenset({cata for (t, cata) in tmpFrontier if t == term}))
            for term in uniqTerms]


def removeSelectorsFromSexp(sexp, selectors):
    """Remove all selectors from an s-expression.
    Returns a new s-expr with a list of new variables and relative assertions.
    NOTE: it doesn't mantain equisatisfiability, see README for more details.
    """
    if type(sexp) != list:
        return sexp, [], []
    elif (type(sexp) == list
          and len(sexp) > 0
          and type(sexp[0]) == str
          and sexp[0] in selectors):

        # the selector and its constructor
        sel = selectors[sexp[0]]
        con = sel.constructor

        # if the constructor is nullary, do nothing as we don't know the
        # value of a selector applied to it
        if not con.isNullary():

            # the argument of the selector
            term, newVarDecls, newAssertions = removeSelectorsFromSexp(
                sexp[1], selectors)

            # Create the fresh variables
            newVars = [(createNewVarName(sel.return_type), sel.return_type)
                       for sel in con.selectors]

            newVarsNames = [v for (v, _) in newVars]

            for (vName, vSort) in newVars:
                """
                ( declare-const <symbol> <sort> )
                """
                newVarDecls.append(
                    ['declare-const', vName, vSort]
                )

            newAssertions.append(["assert", ["=", term, [con.name] + newVarsNames]])

            # Substitute the selector with the correct fresh variable
            sexp = newVarsNames[sel.index]

            return sexp, newVarDecls, newAssertions
    else:
        varDecls = []
        assertions = []
        res = []
        for s in sexp:
            tmpSexp, tmpVarDecls, tmpAssertions = removeSelectorsFromSexp(
                s, selectors)

            varDecls.extend(tmpVarDecls)
            assertions.extend(tmpAssertions)
            res.append(tmpSexp)
        return res, varDecls, assertions


def removeSelectors(script, datatypes):
    """ Remove all selectors from a .cata script, returns a new valid .cata with no selectors.
    NOTE: it doesn't mantain equisatisfiability, see README for more details.
    """
    selectors = {}
    for _, dt in datatypes.items():
        for con in dt.constructors:
            for sel in con.selectors:
                selectors[sel.name] = sel

    res = []
    for sexp in script:
        if sexp[0] == "assert":
            tmpSexp, tmpVarDecls, tmpVarAssertions = removeSelectorsFromSexp(
                sexp, selectors)
            res.extend(tmpVarDecls)
            res.append(tmpSexp)
            res.extend(tmpVarAssertions)
        else:
            res.append(sexp)

    return res


def partialEvaluationSexp(sexp, allCatas):
    """Partially evaluate all catamorphisms in a s-expression.
    E.g.
    (+ (Length Nil) (Length (Cons 2 Nil))) ---> (+ 0 (1 + 0))
    """
    if type(sexp) != list:
        return sexp
    elif (type(sexp) == list
          and len(sexp) > 0
          and type(sexp[0]) == str
          and sexp[0] in allCatas):

        cata = allCatas[sexp[0]]
        term = sexp[1]
        try:
            if type(term) == list:
                # If term is constructed by some non-nullary constructor
                con = [c for c in allCatas[sexp[0]].input_type.constructors
                       if c.name == term[0]][0]
                (defVars, defCon) = cata.defByCon[con]
                tmpTerm = subListInSexp(defCon, list(zip(defVars, term[1:])))

                return partialEvaluationSexp(tmpTerm, allCatas)
            else:
                maybeCon = [c for c in allCatas[sexp[0]].input_type.constructors
                            if c.name == term]
                if maybeCon:
                    # If term is constructed by a nullary constructor
                    tmpTerm = cata.defByCon[maybeCon[0]][1]
                    return partialEvaluationSexp(tmpTerm, allCatas)
                else:
                    # If term is a variable (or just badly constructed)
                    return sexp
        except IndexError:
            raise Exception("Term not well formed: {}" .format(term))
    else:
        res = []
        for s in sexp:
            res.append(partialEvaluationSexp(s, allCatas))
        return res


def partialEvaluation(script, allCatas):
    """ Partially evaluate all catamorphisms in a .cata script, returns a new valid .cata script.
    """
    return [partialEvaluationSexp(sexp, allCatas) for sexp in script]


def writeScriptToFile(mFile, script):
    print("Saving SMT-LIB file to: ", mFile.name)
    with mFile as out:
        out.write("\n".join([print_sexp(sexp) for sexp in script]))

def main():
    # TODO: README

    # TODO: remove superfluous "and" when just one range/control condition

    # New examples?
    # - sum and max?
    # - min, sum, len? In the constraint 2*r1 -> r3 * r1

    # Maybe useful?
    # https://stackoverflow.com/questions/39882992/how-to-get-the-declaration-from-a-z3-smtlib2-formula

    parser = argparse.ArgumentParser(description="An implementation of a semidecision procedure for catamorphisms.")

    parser.add_argument("cataFile", metavar="file",
                        type=argparse.FileType('r'),
                        help="A .cata file, or any text file written with the CataSat syntax (see README)")
    parser.add_argument("-v", "--verbose",
                        action="store_true",
                        help="Prints more details, like depth levels and range and control conditions")
    parser.add_argument("-pm", "--print-model",
                        action='store_true',
                        help="If a model is found, print it (implied by --verbose)")
    parser.add_argument("-stf", "--save-tmp-file", type=argparse.FileType('w'),
                        metavar="OUT_FILE",
                        help="Save the temporary .smt2 file produced by CataSat")
    parser.add_argument("-max", "--max-iterations",
                        type=int, default='6',
                        metavar="ITER",
                        help="The max number of iterations to perform")

    parser.add_argument("-npev", "--no-partial-evaluation",
                        action="store_true",
                        help="Disable partial evaluation of the catamorphisms")
    parser.add_argument("-ss", "--strict-selectors",
                        action='store_true',
                        help="Enable strict selectors (see README)")


    args = parser.parse_args()

    # Enclose everything in a big s-expression
    sexp = ""
    with args.cataFile as f:
        for line in f:
            # Remove comments
            tmpLine = line.split(";", 1)[0]
            sexp = sexp + tmpLine
    sexp = "(" +sexp + ")"

    parsed = parse_sexp(sexp)

    # Reset variable name generator's counter
    createNewVarName.counter = 0

    """
    Skel:
        the parsed smt2 file with catamorphism replaced by uninterpreted functions
    allCatas:
        a dictionary of catamorphisms, the keys are the names of the catamorphisms
    datatypes:
        a dictionary of datatypes, the keys are the names of the datatypes
    rangeConstr:
        a "dictionary" of the range constraints, the "keys" are sets of catamorphisms
        (implemented as a class because we can't use sets as keys for dicts)
        TODO: maybe use frozenset
    """
    skel, allCatas, datatypes, rangeConstr = parseCatas(parsed)

    # Remove all selectors
    if args.strict_selectors:
        skel = removeSelectors(skel, datatypes)

    # Partially evalutate the catamorphisms
    if not args.no_partial_evaluation:
        skel = partialEvaluation(skel, allCatas)

    # The initial frontier is the set of all the arguments of the catamorphisms
    assertions = [s for s in skel if s[0] == "assert"]
    frontier = groupFrontier(findCatamorphismsArguments(assertions, allCatas))

    if args.verbose:
        print("# Depth:  0")

    # If the frontier is empty, there are no control (or range) conditions,
    # so a SAT result is sound
    if frontier == []:
        ckSat, slvr = checkSat(skel)
        if ckSat == z3.sat:
            print("*********")
            print("   SAT   ")
            print("*********")

            if args.print_model:
                print("Model:")
                print_model(slvr.model(), parsed)
                print("*********")

            if args.save_tmp_file:
                writeScriptToFile(args.save_tmp_file, skel)

            return slvr

    # Compute the range conditions
    # \land {for (t, {c_1, \ldots, c_n}) \in F}
    #     R_{c_1, ..., c_n} (c_1(t), ..., c_n(t))
    rangeConditions = []
    for (term, catas) in frontier:
        for (rc_vars, rc_form) in rangeConstr.getFromSet(catas):
            substList = [(var, [cata, term]) for (var, cata) in rc_vars]
            rangeConditions.append(subListInSexp(rc_form, substList))
    if rangeConditions:
        rangeConditions = [["assert", ["and"] + rangeConditions]]
    if args.verbose:
        print("Range Conditions:")
        printSexp(rangeConditions)
        print()

    # If unsatisfiable, return UNSAT
    if checkSat(skel + rangeConditions)[0] == z3.unsat:
        print("*********")
        print("  UNSAT  ")
        print("*********")

        if args.save_tmp_file:
            writeScriptToFile(args.save_tmp_file, skel + rangeConditions)

        return skel + rangeConditions

    # Otherwise, begin with the unrolling
    for i in range(1, args.max_iterations+1):
        if args.verbose:
            print("# Depth: ", i)

        """ Compute the unroll """
        # The declarations of the fresh variables introduced by the unrolling
        # ( declare-fun <symbol> ( <sort>∗ ) <sort> )
        newVariablesDefinitions = []

        # The fresh variables introduced by the unrolling that need to be added
        # to the frontier
        newVarsFrontier = []

        # The unrolling of the formula
        unroll = []

        for (term, catas) in frontier:
            (tNewVariablesDefinitions,
             tNewVarsFrontier,
             tUnroll) = unrollTermCatas(term, catas, allCatas)

            newVariablesDefinitions.extend(tNewVariablesDefinitions)
            newVarsFrontier.extend(tNewVarsFrontier)
            unroll.append(["assert", tUnroll])

        # Updates the script with the unrolling and new variables
        skel.extend(newVariablesDefinitions)
        skel.extend(unroll)

        # Updates the frontier
        oldFrontier = frontier.copy()
        # frontier = newVarsFrontier.copy()
        frontier = groupFrontier(newVarsFrontier)


        # Compute the range conditions on the NEW frontier
        #     \land {for (t, {c_1, \ldots, c_n}) \in F_n}
        #         R_{c_1, ..., c_n} (c_1(t), ..., c_n(t))
        rangeConditions = []
        for (term, catas) in frontier:
            for (rc_vars, rc_form) in rangeConstr.getFromSet(catas):
                substList = [(var, [cata, term]) for (var, cata) in rc_vars]
                rangeConditions.append(subListInSexp(rc_form, substList))
        if rangeConditions:
            rangeConditions = [["assert", ["and"] + rangeConditions]]

        if args.verbose:
            print("Range Conditions:")
            printSexp(rangeConditions)
            print()

        # If unsatisfiable, return UNSAT
        # Otherwise, perform the unrolling
        if checkSat(skel + rangeConditions)[0] == z3.unsat:
            print("*********")
            print("  UNSAT  ")
            print("*********")

            if args.save_tmp_file:
                writeScriptToFile(args.save_tmp_file, skel + rangeConditions)

            return

        # Control conditions are needed to check only the `nodes` of the tableau with an empty frontier,
        # i.e. nodes that do not have "free" variables
        # Compute the control conditions on the OLD frontier
        #     \land {for (t, c) \in F_{n-1}}
        #         \lor {C nullary constructor of the sort of the term t}
        #             t = C
        controlConditions = ["and"]
        for (term, catas) in oldFrontier:
            sort = list(catas)[0].input_type
            termCtrlCond = ["or"]
            nullConstructors = [con for con in sort.constructors
                                if con.isNullary()]
            for con in nullConstructors:
                termCtrlCond.append(["=", term, con.name])

            controlConditions.append(termCtrlCond)

        if args.verbose:
            print("Control Conditions:")
            printSexp([controlConditions])
            print()

        # If satisfiable with control conditions, return SAT
        ckSat, slvr = checkSat(skel + [["assert", controlConditions]])
        if ckSat == z3.sat:
            print("*********")
            print("   SAT   ")
            print("*********")

            if args.print_model or args.verbose:
                print("Model:")
                print_model(slvr.model(), parsed)
                print("*********")

            if args.save_tmp_file:
                writeScriptToFile(args.save_tmp_file,
                                  skel + [["assert", controlConditions]])

            return slvr

    print("*********")
    print("   UNKNOWN   ")
    print("   Max iterations reached: ", args.max_iterations)
    print("*********")


if __name__ == '__main__':
    main()
