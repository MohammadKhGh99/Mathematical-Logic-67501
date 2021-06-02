# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: propositions/semantics.py

"""Semantic analysis of propositional-logic constructs."""

from typing import AbstractSet, Iterable, Iterator, Mapping, Sequence, Tuple

from propositions.syntax import *
from propositions.proofs import *
import itertools as it

#: A model for propositional-logic formulas, a mapping from variable names to
#: truth values.
Model = Mapping[str, bool]


def is_model(model: Model) -> bool:
    """Checks if the given dictionary is a model over some set of variables.

    Parameters:
        model: dictionary to check.

    Returns:
        ``True`` if the given dictionary is a model over some set of variables,
        ``False`` otherwise.
    """
    for key in model:
        if not is_variable(key):
            return False
    return True


def variables(model: Model) -> AbstractSet[str]:
    """Finds all variables over which the given model is defined.

    Parameters:
        model: model to check.

    Returns:
        A set of all variables over which the given model is defined.
    """
    assert is_model(model)
    return model.keys()


def evaluate(formula: Formula, model: Model) -> bool:
    """Calculates the truth value of the given formula in the given model.

    Parameters:
        formula: formula to calculate the truth value of.
        model: model over (possibly a superset of) the variables of the formula,
            to calculate the truth value in.

    Returns:
        The truth value of the given formula in the given model.

    Examples:
        # >>> evaluate(Formula.parse('~(p&q76)'), {'p': True, 'q76': False})
        True

        # >>> evaluate(Formula.parse('~(p&q76)'), {'p': True, 'q76': True})
        False
    """
    assert is_model(model)
    assert formula.variables().issubset(variables(model))
    # Task 2.1
    if is_unary(formula.root):
        return not evaluate(formula.first, model)
    elif formula.root == '&':
        return evaluate(formula.first, model) and evaluate(formula.second, model)
    elif formula.root == '|':
        return evaluate(formula.first, model) or evaluate(formula.second, model)
    elif formula.root == "->":
        first = evaluate(formula.first, model)
        second = evaluate(formula.second, model)
        if (first and second) or (not first and (second or not second)):
            return True
        else:
            return False
    elif formula.root == '+':
        first = evaluate(formula.first, model)
        second = evaluate(formula.second, model)
        if (first and not second) or (not first and second):
            return True
        else:
            return False
    elif formula.root == "<->":
        first = evaluate(formula.first, model)
        second = evaluate(formula.second, model)
        if (first and second) or (not first and not second):
            return True
        else:
            return False
    elif formula.root == "-&":
        first = evaluate(formula.first, model)
        second = evaluate(formula.second, model)
        return not (first and second)
    elif formula.root == "-|":
        first = evaluate(formula.first, model)
        second = evaluate(formula.second, model)
        return not (first or second)
    elif is_constant(formula.root):
        return True if formula.root == 'T' else False
    elif is_variable(formula.root):
        return model[formula.root]


def all_models(variables: Sequence[str]) -> Iterable[Model]:
    """Calculates all possible models over the given variables.

    Parameters:
        variables: variables over which to calculate the models.

    Returns:
        An iterable over all possible models over the given variables. The order
        of the models is lexicographic according to the order of the given
        variables, where False precedes True.

    Examples:
        # >>> list(all_models(['p', 'q']))
        [{'p': False, 'q': False}, {'p': False, 'q': True}, {'p': True, 'q': False}, {'p': True, 'q': True}]

        # >>> list(all_models(['q', 'p']))
        [{'q': False, 'p': False}, {'q': False, 'p': True}, {'q': True, 'p': False}, {'q': True, 'p': True}]
    """
    for v in variables:
        assert is_variable(v)
    # Task 2.2

    truth = [False, True]
    combinations = list(it.product(truth, repeat=len(variables)))
    models = list()
    for comb in combinations:
        model = dict()
        for i in range(len(variables)):
            model[variables[i]] = comb[i]
        models.append(model)
    return models


def truth_values(formula: Formula, models: Iterable[Model]) -> Iterable[bool]:
    """Calculates the truth value of the given formula in each of the given
    model.

    Parameters:
        formula: formula to calculate the truth value of.
        models: iterable over models to calculate the truth value in.

    Returns:
        An iterable over the respective truth values of the given formula in
        each of the given models, in the order of the given models.

    Examples:
        # >>> list(truth_values(Formula.parse('~(p&q76)'), all_models(['p', 'q76'])))
        [True, True, True, False]
    """
    # Task 2.3

    values = list()
    for model in models:
        values.append(evaluate(formula, model))
    return values


def _get_variables(formula, all_variables):
    if is_variable(formula.root):
        all_variables.append(formula.root)
    elif is_unary(formula.root):
        _get_variables(formula.first, all_variables)
    elif is_binary(formula.root):
        _get_variables(formula.first, all_variables)
        _get_variables(formula.second, all_variables)


def print_truth_table(formula: Formula) -> None:
    """Prints the truth table of the given formula, with variable-name columns
    sorted alphabetically.

    Parameters:
        formula: formula to print the truth table of.

    Examples:
        # >>> print_truth_table(Formula.parse('~(p&q76)'))
        | p | q76 | ~(p&q76) |
        |---|-----|----------|
        | F | F   | T        |
        | F | T   | T        |
        | T | F   | T        |
        | T | T   | F        |
    """
    # Task 2.4

    all_variables = list()
    _get_variables(formula, all_variables)
    all_variables = sorted(all_variables)
    models = all_models(all_variables)
    table_results = list(truth_values(formula, models))
    line = "| "
    sep = "|"
    for i in range(len(all_variables)):
        line += all_variables[i] + " | "
        sep += ('-' * (len(all_variables[i]) + 2)) + '|'
    line += str(formula) + " |"
    sep += ((len(str(formula)) + 2) * '-') + '|'
    print(line)
    print(sep)
    for i, model in enumerate(models):
        line = "| "
        for val in model.items():
            if val[1]:
                line += "T" + (" " * (len(val[0]) - 1)) + " | "
            else:
                line += "F" + (" " * (len(val[0]) - 1)) + " | "
        if table_results[i]:
            line += "T" + (" " * (len(str(formula)) - 1)) + " |"
        else:
            line += "F" + (" " * (len(str(formula)) - 1)) + " |"
        print(line)


def is_tautology(formula: Formula) -> bool:
    """Checks if the given formula is a tautology.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a tautology, ``False`` otherwise.
    """
    # Task 2.5a

    all_variables = list()
    _get_variables(formula, all_variables)
    all_variables = list(set(all_variables))
    models = all_models(all_variables)
    table_results = truth_values(formula, models)
    if False in table_results:
        return False
    else:
        return True


def is_contradiction(formula: Formula) -> bool:
    """Checks if the given formula is a contradiction.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a contradiction, ``False`` otherwise.
    """
    # Task 2.5b

    all_variables = list()
    _get_variables(formula, all_variables)
    models = all_models(all_variables)
    table_results = truth_values(formula, models)
    if True in table_results:
        return False
    else:
        return True


def is_satisfiable(formula: Formula) -> bool:
    """Checks if the given formula is satisfiable.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is satisfiable, ``False`` otherwise.
    """
    # Task 2.5c

    all_variables = list()
    _get_variables(formula, all_variables)
    models = all_models(all_variables)
    table_results = truth_values(formula, models)
    if True in table_results:
        return True
    else:
        return False


def _synthesize_for_model(model: Model) -> Formula:
    """Synthesizes a propositional formula in the form of a single conjunctive
    clause that evaluates to ``True`` in the given model, and to ``False`` in
    any other model over the same variables.

    Parameters:
        model: model over a nonempty set of variables, in which the synthesized
            formula is to hold.

    Returns:
        The synthesized formula.
    """
    assert is_model(model)
    assert len(model.keys()) > 0
    # Task 2.6

    form_str = ""
    for i, item in enumerate(model.items()):
        if item[1] is False:
            form_str += "~" + item[0]
        elif item[1]:
            form_str += item[0]
        if i % 2 == 1:
            form_str = '(' + form_str + ')'
        if i + 1 < len(model):
            form_str += "&"
    if form_str.count('&') > 1:
        form_str = '(' + form_str + ')'
    return Formula.parse(form_str)


def synthesize(variables: Sequence[str], values: Iterable[bool]) -> Formula:
    """
    Synthesizes a propositional formula in DNF over the given variables,
    that has the specified truth table.

    Parameters:
        variables: nonempty set of variables for the synthesized formula.
        values: iterable over truth values for the synthesized formula in every
            possible model over the given variables, in the order returned by
            `all_models`\ ``(``\ `~synthesize.variables`\ ``)``.

    Returns:
        The synthesized formula.

    Examples:
        # >>> formula = synthesize(['p', 'q'], [True, True, True, False])
        # >>> for model in all_models(['p', 'q']):
        # ...     evaluate(formula, model)
        True
        True
        True
        False
    """
    assert len(variables) > 0
    # Task 2.7

    form_str = ""
    models = all_models(variables)
    for i, val in enumerate(values):
        if val:
            cur_form = str(_synthesize_for_model(list(models)[i]))
            if cur_form[0] != '(' and cur_form[-1] != ')' and '&' in cur_form:
                cur_form = '(' + cur_form + ')'
            form_str += cur_form
            more_true = True in list(values)[i + 1:]
            if more_true:
                if i >= 1:
                    form_str = '(' + form_str + ')'
                form_str += '|'

    if form_str.count('|') >= 1:
        form_str = '(' + form_str + ')'
    if form_str == "":
        form_str = '(' + variables[0] + '&~' + variables[0] + ')'
    return Formula.parse(form_str)


def _synthesize_for_all_except_model(model: Model) -> Formula:
    """Synthesizes a propositional formula in the form of a single disjunctive
    clause that evaluates to ``False`` in the given model, and to ``True`` in
    any other model over the same variables.

    Parameters:
        model: model over a nonempty set of variables, in which the synthesized
            formula is to hold.

    Returns:
        The synthesized formula.
    """
    assert is_model(model)
    assert len(model.keys()) > 0
    # Optional Task 2.8


def synthesize_cnf(variables: Sequence[str], values: Iterable[bool]) -> Formula:
    """
    Synthesizes a propositional formula in CNF over the given variables,
    that has the specified truth table.

    Parameters:
        variables: nonempty set of variables for the synthesized formula.
        values: iterable over truth values for the synthesized formula in every
            possible model over the given variables, in the order returned by
            `all_models`\ ``(``\ `~synthesize.variables`\ ``)``.

    Returns:
        The synthesized formula.

    Examples:
        # >>> formula = synthesize_cnf(['p', 'q'], [True, True, True, False])
        # >>> for model in all_models(['p', 'q']):
        # ...     evaluate(formula, model)
        True
        True
        True
        False
    """
    assert len(variables) > 0
    # Optional Task 2.9


# Tasks for Chapter 4

def evaluate_inference(rule: InferenceRule, model: Model) -> bool:
    """Checks if the given inference rule holds in the given model.

    Parameters:
        rule: inference rule to check.
        model: model to check in.

    Returns:
        ``True`` if the given inference rule holds in the given model, ``False``
        otherwise.

    Examples:
        >>> evaluate_inference(InferenceRule([Formula('p')], Formula('q')),
        ...                    {'p': True, 'q': False})
        False

        >>> evaluate_inference(InferenceRule([Formula('p')], Formula('q')),
        ...                    {'p': False, 'q': False})
        True
    """
    assert is_model(model)
    # Task 4.2

    result = True
    for assume in rule.assumptions:
        result = evaluate(assume, model) & result
    if result:
        root1 = "T"
    else:
        root1 = "F"
    if evaluate(rule.conclusion, model):
        root2 = "T"
    else:
        root2 = "F"
    return evaluate(Formula("->", Formula(root1), Formula(root2)), model)


def is_sound_inference(rule: InferenceRule) -> bool:
    """Checks if the given inference rule is sound, i.e., whether its
    conclusion is a semantically correct implication of its assumptions.

    Parameters:
        rule: inference rule to check.

    Returns:
        ``True`` if the given inference rule is sound, ``False`` otherwise.
    """
    # Task 4.3

    my_set = set()
    for assume in rule.assumptions:
        my_set.update(assume.variables())
    my_set.update(rule.conclusion.variables())
    models = all_models(list(my_set))
    txt = ""
    for model in models:
        txt += str(evaluate_inference(rule, model)) + " and "
    txt = txt[:-5]
    return True if eval(txt) else False
