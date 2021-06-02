# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: predicates/functions.py

"""Syntactic conversion of predicate-logic formulas to not use functions and
equality."""

from typing import AbstractSet, List, Set

from logic_utils import fresh_variable_name_generator as fresh

from predicates.syntax import *
from predicates.semantics import *


def function_name_to_relation_name(function: str) -> str:
    """Converts the given function name to a canonically corresponding relation
    name.

    Parameters:
        function: function name to convert.

    Returns:
        A relation name that is the same as the given function name, except that
        its first letter is capitalized.
    """
    assert is_function(function)
    return function[0].upper() + function[1:]


def relation_name_to_function_name(relation: str) -> str:
    """Converts the given relation name to a canonically corresponding function
    name.

    Parameters:
        relation: relation name to convert.

    Returns:
        A function name `function` such that
        `function_name_to_relation_name`\ ``(``\ `function`\ ``)`` is the given
        relation name.
    """
    assert is_relation(relation)
    return relation[0].lower() + relation[1:]


def replace_functions_with_relations_in_model(model: Model[T]) -> Model[T]:
    """Converts the given model to a canonically corresponding model without any
    function meanings, replacing each function meaning with a canonically
    corresponding relation meaning.

    Parameters:
        model: model to convert, such that there exist no canonically
            corresponding function name and relation name that both have
            meanings in this model.

    Returns:
        A model obtained from the given model by replacing every function
        meaning of a function name with a relation meaning of the canonically
        corresponding relation name, such that the relation meaning contains
        any tuple ``(``\ `x1`\ ``,``...\ ``,``\ `xn`\ ``)``  if and only if `x1`
        is the output of the function meaning for the arguments
        ``(``\ `x2`\ ``,``...\ ``,``\ `xn`\ ``)``.
    """
    for function in model.function_meanings:
        assert function_name_to_relation_name(function) not in \
               model.relation_meanings
    # Task 8.1

    new_relations = dict(model.relation_meanings)
    for item in model.function_meanings.items():
        new_meanings = {(meaning[1],) + meaning[0] for meaning in item[1].items()}
        new_relations[function_name_to_relation_name(item[0])] = new_meanings
    return Model(model.universe, model.constant_meanings, new_relations, frozendict())


def replace_relations_with_functions_in_model(model: Model[T], original_functions: AbstractSet[str]) -> \
        Union[Model[T], None]:
    """Converts the given model with no function meanings to a canonically
    corresponding model with meanings for the given function names, having each
    new function meaning replace a canonically corresponding relation meaning.

    Parameters:
        model: model to convert, that contains no function meanings.
        original_functions: function names for the model to convert to,
            such that no relation name that canonically corresponds to any of
            these function names has a meaning in the given model.

    Returns:
        A model `model` with the given function names such that
        `replace_functions_with_relations_in_model`\ ``(``\ `model`\ ``)``
        is the given model, or ``None`` if no such model exists.
    """
    for function in original_functions:
        assert is_function(function)
        assert function not in model.function_meanings
        assert function_name_to_relation_name(function) in \
               model.relation_meanings
    # Task 8.2

    new_relations = dict()
    new_functions = dict(model.function_meanings)
    for item in model.relation_meanings.items():
        function = relation_name_to_function_name(item[0])
        new_meanings = dict()
        if function in original_functions:
            if len(model.universe) ** len(list(item[1])[0][1:]) != len(item[1]):
                return None
            for meaning in item[1]:
                if meaning[1:] in new_meanings.keys():
                    return None
                new_meanings[meaning[1:]] = str(meaning[0])
            new_functions[function] = new_meanings
        else:
            new_relations[item[0]] = item[1]

    return Model(model.universe, model.constant_meanings, new_relations, new_functions)


def _compile_term(term: Term) -> List[Formula]:
    """Syntactically compiles the given term into a list of single-function
    invocation steps.

    Parameters:
        term: term to compile, whose root is a function invocation, and which
            contains no variable names starting with ``z``.

    Returns:
        A list of steps, each of which is a formula of the form
        ``'``\ `y`\ ``=``\ `f`\ ``(``\ `x1`\ ``,``...\ ``,``\ `xn`\ ``)'``,
        where `y` is a new variable name obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``, `f`
        is a function name, and each of the `x`\ `i` is either a constant name
        or a variable name. If `x`\ `i` is a new variable name, then it is also
        the left-hand side of a previous step, where all of the steps "leading
        up to" `x1` precede those "leading up" to `x2`, etc. If all the returned
        steps hold in any model, then the left-hand-side variable of the last
        returned step evaluates in that model to the value of the given term.
    """
    assert is_function(term.root)
    for variable in term.variables():
        assert variable[0] != 'z'
    # Task 8.3

    arguments, all_formulas = list(), list()
    for argument in term.arguments:
        if not is_function(argument.root):
            arguments.append(argument)
        else:
            result = _compile_term(argument)
            arguments.append(result[-1].arguments[0])
            all_formulas += result
    all_formulas.append(Formula('=', [Term(next(fresh)), Term(term.root, arguments)]))
    return all_formulas


def _equality_helper(formula: Formula, relation: str, arguments, new_args) -> Formula:
    if len(arguments) == 0:
        return Formula(relation, new_args) if is_relation(formula.root) else Formula('=', new_args)
    if not is_function(arguments[0].root):
        return _equality_helper(formula, relation, arguments[1:], new_args + [arguments[0]])
    new_formulas = _compile_term(arguments[0])[::-1]
    new_args.append(new_formulas[0].arguments[0])
    predicate = None
    predicate = Formula('=', new_args) if len(arguments) == 1 and is_equality(formula.root) else predicate
    predicate = Formula(relation, new_args) if len(arguments) == 1 and is_relation(formula.root) else predicate
    if predicate is None:
        predicate = _equality_helper(formula, relation, arguments[1:], new_args) if len(arguments) != 1 else predicate
    for i in range(len(new_formulas)):
        relation = function_name_to_relation_name(new_formulas[i].arguments[1].root)
        first_form = Formula(relation, (new_formulas[i].arguments[0],) + new_formulas[i].arguments[1].arguments)
        predicate = Formula('A', str(new_formulas[i].arguments[0]), Formula('->', first_form, predicate))
    return predicate


def replace_functions_with_relations_in_formula(formula: Formula) -> Formula:
    """Syntactically converts the given formula to a formula that does not
    contain any function invocations, and is "one-way equivalent" in the sense
    that the former holds in a model if and only if the latter holds in the
    canonically corresponding model with no function meanings.

    Parameters:
        formula: formula to convert, which contains no variable names starting
            with ``z``, and such that there exist no canonically corresponding
            function name and relation name that are both invoked in this
            formula.

    Returns:
        A formula such that the given formula holds in any model `model` if and
        only if the returned formula holds in
        `replace_function_with_relations_in_model`\ ``(``\ `model`\ ``)``.
    """
    assert len({function_name_to_relation_name(function) for
                function, arity in formula.functions()}.intersection(
        {relation for relation, arity in formula.relations()})) == 0
    for variable in formula.variables():
        assert variable[0] != 'z'
    # Task 8.4

    if is_binary(formula.root):
        first_result = replace_functions_with_relations_in_formula(formula.first)
        return Formula(formula.root, first_result, replace_functions_with_relations_in_formula(formula.second))
    elif is_unary(formula.root):
        return Formula(formula.root, replace_functions_with_relations_in_formula(formula.first))
    elif is_quantifier(formula.root):
        return Formula(formula.root, formula.variable, replace_functions_with_relations_in_formula(formula.predicate))
    elif is_equality(formula.root) or is_relation(formula.root):
        return _equality_helper(formula, formula.root, formula.arguments, list())


def replace_functions_with_relations_in_formulas(formulas: AbstractSet[Formula]) -> Set[Formula]:
    """Syntactically converts the given set of formulas to a set of formulas
    that do not contain any function invocations, and is "two-way
    equivalent" in the sense that:

    1. The former holds in a model if and only if the latter holds in the
       canonically corresponding model with no function meanings.
    2. The latter holds in a model if and only if that model has a
       canonically corresponding model with meanings for the functions of the
       former, and the former holds in that model.

    Parameters:
        formulas: formulas to convert, which contain no variable names starting
            with ``z``, and such that there exist no canonically corresponding
            function name and relation name that are both invoked in these
            formulas.

    Returns:
        A set of formulas, one for each given formula as well as one additional
        formula for each relation name that replaces a function name from the
        given formulas, such that:

        1. The given formulas hold in a model `model` if and only if the
           returned formulas hold in
           `replace_functions_with_relations_in_model`\ ``(``\ `model`\ ``)``.
        2. The returned formulas hold in a model `model` if and only if
           `replace_relations_with_functions_in_model`\ ``(``\ `model`\ ``,``\ `original_functions`\ ``)``,
           where `original_functions` are all the function names in the given
           formulas, is a model and the given formulas hold in it.
    """
    assert len(set.union(*[{function_name_to_relation_name(function) for
                            function, arity in formula.functions()}
                           for formula in formulas]).intersection(
        set.union(*[{relation for relation, arity in
                     formula.relations()} for
                    formula in formulas]))) == 0
    for formula in formulas:
        for variable in formula.variables():
            assert variable[0] != 'z'
    # Task 8.5

    all_formulas = [replace_functions_with_relations_in_formula(formula) for formula in formulas]
    for formula in formulas:
        for name, num in formula.functions():
            relation, term = function_name_to_relation_name(name), Term.parse(next(fresh))
            arguments = tuple(Term.parse(next(fresh)) for _ in range(num))
            predicate = Formula('E', str(term), Formula(relation, (term,) + arguments))
            if len(arguments) > 0:
                predicate = [Formula('A', str(arg), predicate) for arg in arguments][-1]
            all_formulas += [predicate]
            term1, term2 = Term.parse(next(fresh)), Term.parse(next(fresh))
            first, second = Formula(relation, (term1,) + arguments), Formula(relation, (term2,) + arguments)
            predicate = Formula('->', Formula('&', first, second), Formula('=', [term1, term2]))
            arguments = (term1, term2) + arguments
            all_formulas += [[Formula('A', str(arg), predicate) for arg in arguments][-1]]
    return set(all_formulas)


def replace_equality_with_SAME_in_formulas(formulas: AbstractSet[Formula]) -> \
        Set[Formula]:
    """Syntactically converts the given set of formulas to a canonically
    corresponding set of formulas that do not contain any equalities, consisting
    of the following formulas:

    1. A formula for each of the given formulas, where each equality is
       replaced with a matching invocation of the relation name ``'SAME'``.
    2. Formula(s) that ensure that in any model for the returned formulas,
       the meaning of the relation name ``'SAME'`` is reflexive, symmetric, and
       transitive.
    3. For each relation name from the given formulas, formula(s) that ensure
       that in any model for the returned formulas, the meaning of this
       relation name respects the meaning of the relation name ``'SAME'``.

    Parameters:
        formulas: formulas to convert, that contain no function names and do not
            contain the relation name ``'SAME'``.

    Returns:
        The converted set of formulas.
    """
    for formula in formulas:
        assert len(formula.functions()) == 0
        assert 'SAME' not in \
               {relation for relation, arity in formula.relations()}
    # Task 8.6

    answer = set()
    # do symmetry reflexivity transitivity
    answer.add(reflexivity())
    answer.add(symmetry())
    answer.add(transitivity())

    # change equality to SAME
    for formula in formulas:
        answer.add(replace_same(formula))

        # do relations
        for relation_name, arities in formula.relations():
            answer.add(relations_SAME(relation_name, arities))

    return answer


def replace_same(formula: Formula):
    if is_equality(formula.root):
        return Formula('SAME', [formula.arguments[0], formula.arguments[1]])

    elif is_relation(formula.root):
        return formula

    elif is_binary(formula.root):
        first = replace_same(formula.first)
        second = replace_same(formula.second)
        return Formula(formula.root, first, second)

    elif is_unary(formula.root):
        first = replace_same(formula.first)
        return Formula(formula.root, first)

    elif is_quantifier(formula.root):
        predicate = replace_same(formula.predicate)
        return Formula(formula.root, formula.variable, predicate)


def reflexivity():
    args = Term(next(fresh))
    return Formula('A', str(args), Formula('SAME', [args, args]))


def symmetry():
    args = [Term(next(fresh)) for i in range(2)]

    # (x,y)
    formula_xy = Formula('SAME', args)
    # (y,x)
    formula_yx = Formula('SAME', args[::-1])
    # (x,y)->(y,x) & (y,x)->(x,y)
    formula_xy_yx = Formula('&', Formula('->', formula_xy, formula_yx), Formula('->', formula_yx, formula_xy))

    return Formula('A', str(args[0]), Formula('A', str(args[1]), formula_xy_yx))


def transitivity():
    args = [Term(next(fresh)) for i in range(3)]

    # (x,y)
    formula_xy = Formula('SAME', args[:2])
    # (y,x)
    formula_yx = Formula('SAME', args[1:3])
    # (x,y)->(y,x) & (y,x)->(x,y)
    formula_xy_yx = Formula('&', formula_xy, formula_yx)
    formula_xz = Formula('->', formula_xy_yx, Formula('SAME', [args[0], args[2]]))

    return Formula('A', str(args[0]), Formula('A', str(args[1]), Formula('A', str(args[2]), formula_xz)))


def relations_SAME(relation_name, arity):
    """ given a relation_name and its  arity we connect the relation SAME to to its
    intended logical meaning in the given relation"""
    args1 = [Term(next(fresh)) for i in range(arity)]
    args2 = [Term(next(fresh)) for i in range(arity)]

    formulas = []
    for i in range(arity):
        formulas.append(Formula('SAME', [args1[i], args2[i]]))

    # merge all formulas
    merged_formulas = formulas[0]
    for i in range(1, len(formulas)):
        merged_formulas = Formula('&', merged_formulas, formulas[i])

    answer = Formula('->', merged_formulas, Formula('->', Formula(relation_name, args1), Formula(relation_name, args2)))

    # adding for all
    flipped_args = args2[::-1] + args1[::-1]
    for arg in flipped_args:
        answer = Formula('A', str(arg), answer)
    return answer


def add_SAME_as_equality_in_model(model: Model[T]) -> Model[T]:
    """Adds a meaning for the relation name ``'SAME'`` in the given model, that
    canonically corresponds to equality in the given model.

    Parameters:
        model: model that has no meaning for the relation name ``'SAME'``, to
            add the meaning to.

    Returns:
        A model obtained from the given model by adding a meaning for the
        relation name ``'SAME'``, that contains precisely all pairs
        ``(``\ `x`\ ``,``\ `x`\ ``)`` for every element `x` of the universe of
        the given model.
    """
    assert 'SAME' not in model.relation_meanings
    # Task 8.7

    universe = model.universe
    same = set()
    for x in universe:
        same.add((x, x))
    new_model = Model(universe, model.constant_meanings, {**model.relation_meanings, **{'SAME': same}},
                      model.function_meanings)
    return new_model


def get_classes(model):
    all_classes = []
    for x in model.universe:
        for y in model.universe:
            if (x, y) in model.relation_meanings['SAME']:

                found = False
                for the_class in all_classes:
                    if x in the_class:
                        the_class.add(y)
                        found = True
                        break
                    elif y in the_class:
                        the_class.add(x)
                        found = True
                        break
                    else:
                        pass

                if not found:
                    all_classes.append({x, y})

    classes = dict()
    for group in all_classes:
        classes[next(iter(group))] = group
    return classes


def get_key(classes, element):
    for group in classes.items():
        if element in group[1]:
            return group[0]


def make_equality_as_SAME_in_model(model: Model[T]) -> Model[T]:
    """Converts the given model to a model where equality coincides with the
    meaning of ``'SAME'`` in the given model, in the sense that any set of
    formulas holds in the returned model if and only if its canonically
    corresponding set of formulas that do not contain equality holds in the
    given model.

    Parameters:
        model: model to convert, that contains no function meanings, and
            contains a meaning for the relation name ``'SAME'`` that is
            reflexive, symmetric, transitive, and respected by the meanings
            of all other relation names.

    Returns:
        A model that is a model for any set `formulas` if and only if
        the given model is a model for
        `replace_equality_with_SAME`\ ``(``\ `formulas`\ ``)``. The universe of
        the returned model corresponds to the equivalence classes of the
        ``'SAME'`` relation in the given model.
    """
    assert 'SAME' in model.relation_meanings and \
           model.relation_arities['SAME'] == 2
    assert len(model.function_meanings) == 0
    # Task 8.8

    new_constant_meanings = {}
    new_relation_meanings = {}

    classes = get_classes(model)
    new_universe = set(classes.keys())

    for constant_item in model.constant_meanings.items():
        new_constant_meanings[constant_item[0]] = get_key(classes, constant_item[1])

    for relation_item in model.relation_meanings.items():
        if relation_item[0] != 'SAME':
            relations = set()
            for all_elements in relation_item[1]:
                for element in all_elements:
                    relations.add(tuple(get_key(classes, element)))
            new_relation_meanings[relation_item[0]] = relations

    return Model(new_universe, new_constant_meanings, new_relation_meanings)
