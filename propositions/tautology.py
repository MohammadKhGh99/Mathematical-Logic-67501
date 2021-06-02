# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: propositions/tautology.py

"""The Tautology Theorem and its implications."""

from typing import List, Sequence, Union

from logic_utils import frozendict

from propositions.syntax import *
from propositions.semantics import *
from propositions.proofs import *
from propositions.axiomatic_systems import *
from propositions.deduction import *


def formulas_capturing_model(model: Model) -> List[Formula]:
    """Computes the formulas that capture the given model: ``'``\ `x`\ ``'``
    for each variable `x` that is assigned the value ``True`` in the given
    model, and ``'~``\ `x`\ ``'`` for each variable `x` that is assigned the
    value ``False``.

    Parameters:
        model: model to construct the formulas for.

    Returns:
        A list of the constructed formulas, ordered alphabetically by variable
        name.

    Examples:
        >>> formulas_capturing_model({'p2': False, 'p1': True, 'q': True})
        [p1, ~p2, q]
    """
    assert is_model(model)
    # Task 6.1a

    formulas = list()
    temp = dict(sorted(model.items(), key=lambda v: v[0]))
    for item in temp.items():
        if item[1]:
            formulas.append(Formula(item[0]))
        else:
            formulas.append(Formula('~', Formula(item[0])))
    return formulas


# def prove_in_model(formula, model):
#     """ If formula evaluates to True in model, return a proof of formula from
#         the formulae that capture model as assumption (in the order returned
#         by formulae_capturing_model) via AXIOMATIC_SYSTEM. If formula evaluates
#         to False in model, return a proof of ~formula from the same assumptions
#         via AXIOMATIC_SYSTEM. formula may contain no operators beyond '->' and
#         '~' """
#     assert type(formula) is Formula
#     assert formula.operators().issubset({'->', '~'})
#     assert is_model(model)
#     # Task 6.1b
#     assumptions = formulas_capturing_model(model)
#     rules = AXIOMATIC_SYSTEM
#     # is formula root is implies (->)
#     if str(formula.root) == '->':
#         if evaluate(formula, model):
#             # the formula evaluates to True
#             if not evaluate(formula.first, model):
#                 # if the first side of implies evaluates to False
#                 # use I3 and (~first) to prove (formula)
#                 first = formula.first
#                 # proving (~first)
#                 p1 = prove_in_model(first, model)
#                 lines = list(p1.lines)
#                 # '(~first->(first->second))'
#                 lines.append(Proof.Line(Formula('->', p1.statement.conclusion, formula), I2, []))
#                 # first->second (proof of formula from the past 2 lines
#                 lines.append(Proof.Line(formula, MP, [len(lines) - 2, len(lines) - 1]))
#                 statement = InferenceRule(assumptions, formula)
#                 return Proof(statement, rules, lines)
#             elif evaluate(formula.second, model):
#                 # if the second side of implies evaluates to True
#                 # use I1 and (second) to prove (formula)
#                 second = formula.second
#                 # proving (second)
#                 p1 = prove_in_model(second, model)
#                 lines = list(p1.lines)
#
#                 # '(second->(first->second))'
#                 lines.append(Proof.Line(Formula('->', p1.statement.conclusion, formula), I1, []))
#
#                 # first->second (proof of formula from the past 2 lines
#                 lines.append(Proof.Line(formula, MP, [len(lines) - 2, len(lines) - 1]))
#
#                 statement = InferenceRule(assumptions, formula)
#                 return Proof(statement, rules, lines)
#             return None
#         else:
#             # the first is True and the second evaluates to False
#             # prove (~formula) by using NI with (first) and (~second)
#             first = formula.first
#             second = formula.second
#             # proving (first)
#             p1 = prove_in_model(first, model)
#             # make the 2nd proof (~second)
#             p2 = prove_in_model(second, model)
#             specialized_NI = NI.specialize({'p':p1.statement.conclusion, 'q':p2.statement.conclusion.first})
#             npp = combine_proofs(p1, p2, specialized_NI.conclusion.second.second, NI)
#             return npp
#     elif is_variable(str(formula.root)):
#         assumptions0 = formulas_capturing_model({str(formula.root):model[str(formula.root)]})
#         # formula is a variable
#         statement = InferenceRule(assumptions, assumptions0[0])
#         return Proof(statement, rules, [Proof.Line(assumptions0[0])])
#     elif is_unary(str(formula.root)):
#         if evaluate(formula, model):
#             # if formula evaluates to True, and its of the form (~first), then first evaluates to false
#             # and so by calling the function to first it'll prove (~first) which is formula, as needed.
#             return prove_in_model(formula.first, model)
#         else:
#             # the formula evaluates to False with the given model, use NN and (first) to prove (~formula)
#             # (~~first) evaluates to true, so does first
#             # proving (first)
#             p1 = prove_in_model(formula.first, model)
#             lines = list(p1.lines)
#             # '(first->~~first)' got it using NN
#             lines.append(Proof.Line(Formula('->', p1.statement.conclusion, Formula('~',formula)), NN, []))
#             # ~(~first) which is exactly ~formula which evaluates to True (proof of formula from the past 2 lines)
#             lines.append(Proof.Line(Formula('~',formula), MP, [len(lines) - 2, len(lines) - 1]))
#             statement = InferenceRule(assumptions, Formula('~', formula))
#             return Proof(statement, rules, lines)
#     return None


def prove_in_model(formula: Formula, model: Model) -> Proof:
    """Either proves the given formula or proves its negation, from the formulas
    that capture the given model.

    Parameters:
        formula: formula that contains no constants or operators beyond ``'->'``
            and ``'~'``, whose affirmation or negation is to prove.
        model: model from whose formulas to prove.

    Returns:
        If the given formula evaluates to ``True`` in the given model, then
        a valid proof of the formula; otherwise a valid proof of
        ``'~``\ `formula`\ ``'``. The returned proof is from the formulas that
        capture the given model, in the order returned by
        `formulas_capturing_model`\ ``(``\ `model`\ ``)``, via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.

    Examples:
        >>> proof = prove_in_model(Formula.parse('(p->q7)'),
        ...                        {'q7': False, 'p': True})
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        ~(p->q7)
        >>> proof.statement.assumptions
        (p, ~q7)
        >>> proof.rules == AXIOMATIC_SYSTEM
        True

        >>> proof = prove_in_model(Formula.parse('(p->q7)'),
        ...                        {'q7': False, 'p': False})
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        (p->q7)
        >>> proof.statement.assumptions
        (~p, ~q7)
        >>> proof.rules == AXIOMATIC_SYSTEM
        True
    """
    assert formula.operators().issubset({'->', '~'})
    assert is_model(model)
    # Task 6.1b

    temp = formulas_capturing_model(model)
    result = evaluate(formula, model)
    if result:
        conclusion = formula
    else:
        conclusion = Formula('~', formula)
    all_variables = formula.variables()
    lines = [Proof.Line(t) for t in temp if len(all_variables.difference(t.variables())) != len(all_variables)]

    if formula.root == "->":
        dic = {'p': formula.first, 'q': formula.second}
        if result:
            if not evaluate(formula.first, model):
                proof = prove_in_model(Formula('~', formula.first), model)
                lines = list(proof.lines)
                i = len(lines) - 1
                lines.append(Proof.Line(I2.conclusion.substitute_variables(dic), I2, []))
                lines.append(Proof.Line(I2.conclusion.second.substitute_variables(dic), MP, [i, i + 1]))
            elif evaluate(formula.second, model):
                proof = prove_in_model(formula.second, model)
                lines = list(proof.lines)
                i = len(lines) - 1
                lines.append(Proof.Line(I1.conclusion.substitute_variables(dic), I1, []))
                lines.append(Proof.Line(I1.conclusion.second.substitute_variables(dic), MP, [i, i + 1]))
        else:
            proof1 = prove_in_model(formula.first, model)
            proof2 = prove_in_model(Formula('~', formula.second), model)
            proof = combine_proofs(proof1, proof2, Formula('~', formula), NI)
            lines = proof.lines
    elif formula.root == '~':
        if result:
            proof = prove_in_model(formula.first, model)
            lines = list(proof.lines)
            i = len(lines) - 1
            temp_formula = I0.conclusion.substitute_variables({'p': formula})
            lines.append(Proof.Line(temp_formula, I0, []))
            lines.append(Proof.Line(temp_formula.second, MP, [i, i + 1]))
        else:
            proof = prove_in_model(formula.first, model)
            lines = list(proof.lines)
            i = len(proof.lines) - 1
            temp_formula = NN.conclusion.substitute_variables({'p': formula.first})
            lines.append(Proof.Line(temp_formula, NN, []))
            lines.append(Proof.Line(temp_formula.second, MP, [i, i + 1]))

    return Proof(InferenceRule(temp, conclusion), AXIOMATIC_SYSTEM, lines)


def reduce_assumption(proof_from_affirmation: Proof,
                      proof_from_negation: Proof) -> Proof:
    """Combines the given two proofs, both of the same formula `conclusion` and
    from the same assumptions except that the last assumption of the latter is
    the negation of that of the former, into a single proof of `conclusion` from
    only the common assumptions.

    Parameters:
        proof_from_affirmation: valid proof of `conclusion` from one or more
            assumptions, the last of which is an assumption `assumption`.
        proof_from_negation: valid proof of `conclusion` from the same
            assumptions and inference rules of `proof_from_affirmation`, but
            with the last assumption being ``'~``\ `assumption` ``'`` instead of
            `assumption`.

    Returns:
        A valid proof of `conclusion` from only the assumptions common to the
        given proofs (i.e., without the last assumption of each), via the same
        inference rules of the given proofs and in addition
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.R`.

    Examples:
        If `proof_from_affirmation` is of ``['p', '~q', 'r'] ==> '(p&(r|~r))'``,
        then `proof_from_negation` must be of
        ``['p', '~q', '~r'] ==> '(p&(r|~r))'`` and the returned proof is of
        ``['p', '~q'] ==> '(p&(r|~r))'``.
    """
    assert proof_from_affirmation.is_valid()
    assert proof_from_negation.is_valid()
    assert proof_from_affirmation.statement.conclusion == \
           proof_from_negation.statement.conclusion
    assert len(proof_from_affirmation.statement.assumptions) > 0
    assert len(proof_from_negation.statement.assumptions) > 0
    assert proof_from_affirmation.statement.assumptions[:-1] == \
           proof_from_negation.statement.assumptions[:-1]
    assert Formula('~', proof_from_affirmation.statement.assumptions[-1]) == \
           proof_from_negation.statement.assumptions[-1]
    assert proof_from_affirmation.rules == proof_from_negation.rules
    # Task 6.2

    conclusion = proof_from_affirmation.statement.conclusion
    remove1 = remove_assumption(proof_from_affirmation)
    remove2 = remove_assumption(proof_from_negation)
    return combine_proofs(remove1, remove2, conclusion, R)


def prove_tautology(tautology: Formula, model: Model = frozendict()) -> Proof:
    """Proves the given tautology from the formulas that capture the given
    model.

    Parameters:
        tautology: tautology that contains no constants or operators beyond
            ``'->'`` and ``'~'``, to prove.
        model: model over a (possibly empty) prefix (with respect to the
            alphabetical order) of the variables of `tautology`, from whose
            formulas to prove.

    Returns:
        A valid proof of the given tautology from the formulas that capture the
        given model, in the order returned by
        `formulas_capturing_model`\ ``(``\ `model`\ ``)``, via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.

    Examples:
        >>> proof = prove_tautology(Formula.parse('(~(p->p)->q)'),
        ...                         {'p': True, 'q': False})
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        (~(p->p)->q)
        >>> proof.statement.assumptions
        (p, ~q)
        >>> proof.rules == AXIOMATIC_SYSTEM
        True

        >>> proof = prove_tautology(Formula.parse('(~(p->p)->q)'))
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        (~(p->p)->q)
        >>> proof.statement.assumptions
        ()
        >>> proof.rules == AXIOMATIC_SYSTEM
        True
    """
    assert is_tautology(tautology)
    assert tautology.operators().issubset({'->', '~'})
    assert is_model(model)
    assert sorted(tautology.variables())[:len(model)] == sorted(model.keys())
    # Task 6.3a

    # formula_vars = sorted(list(tautology.variables()))
    # # num_vars_in_model holds the number of variables in the formula that are also in the model.
    # num_vars_in_model = len([x for x in formula_vars if x in model.keys()])
    # if num_vars_in_model == len(formula_vars):
    #     return prove_in_model(tautology, model)
    # else:
    #     # get both models one witht he value True and one with the value False (for the next missing variable)
    #     affirmation_model = {**model, **{formula_vars[num_vars_in_model]: True}}
    #     negation_model = {**model, **{formula_vars[num_vars_in_model]: False}}
    #     # get both proofs with those assumptions
    #     affirmation_proof = prove_tautology(tautology, affirmation_model)
    #     negation_proof = prove_tautology(tautology, negation_model)
    #     # remove the extra assumption from the proof
    #     return reduce_assumption(affirmation_proof, negation_proof)
    #
    all_variables = tautology.variables()
    # If the given model is over all the variables of the given tautology
    if len(model) >= len(all_variables) and all_variables.issubset(variables(model)):
        return prove_in_model(tautology, model)
    not_in = None
    for v in sorted(all_variables):
        if v not in model.keys():
            not_in = v
            break

    new_dict = dict(model)
    new_dict[not_in] = True
    proof1 = prove_tautology(tautology, new_dict)
    new_dict[not_in] = False
    proof2 = prove_tautology(tautology, new_dict)
    return reduce_assumption(proof1, proof2)


def proof_or_counterexample(formula: Formula) -> Union[Proof, Model]:
    """Either proves the given formula or finds a model in which it does not
    hold.

    Parameters:
        formula: formula that contains no constants or operators beyond ``'->'``
            and ``'~'``, to either prove or find a counterexample for.

    Returns:
        If the given formula is a tautology, then an assumptionless proof of the
        formula via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`,
        otherwise a model in which the given formula does not hold.
    """
    assert formula.operators().issubset({'->', '~'})
    # Task 6.3b

    models = all_models(list(formula.variables()))
    if is_tautology(formula):
        return prove_tautology(formula, frozendict())
    else:
        for model in models:
            if not evaluate(formula, model):
                return model


def encode_as_formula(rule: InferenceRule) -> Formula:
    """Encodes the given inference rule as a formula consisting of a chain of
    implications.

    Parameters:
        rule: inference rule to encode.

    Returns:
        The formula encoding the given rule.

    Examples:
        >>> encode_as_formula(InferenceRule([Formula('p1'), Formula('p2'),
        ...                                  Formula('p3'), Formula('p4')],
        ...                                 Formula('q')))
        (p1->(p2->(p3->(p4->q))))

        >>> encode_as_formula(InferenceRule([], Formula('q')))
        q
    """
    # Task 6.4a

    assumptions = ""
    for assume in rule.assumptions:
        assumptions += '(' + str(assume) + "->"
    assumptions += str(rule.conclusion) + (')' * len(rule.assumptions))
    return Formula.parse(assumptions)


def prove_sound_inference(rule: InferenceRule) -> Proof:
    """Proves the given sound inference rule.

    Parameters:
        rule: sound inference rule whose assumptions and conclusion contain no
            constants or operators beyond ``'->'`` and ``'~'``, to prove.

    Returns:
        A valid proof of the given sound inference rule via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    assert is_sound_inference(rule)
    for formula in rule.assumptions + (rule.conclusion,):
        assert formula.operators().issubset({'->', '~'})
    # Task 6.4b

    formula = encode_as_formula(rule)
    proof = prove_tautology(formula)
    assumes = rule.assumptions
    if len(rule.assumptions) > 0:
        temp = [Proof.Line(assume) for assume in rule.assumptions] + list(proof.lines)
        lines = list()
        for line in temp:
            if not line.is_assumption() and len(line.assumptions) > 0:
                lines.append(Proof.Line(line.formula, line.rule, [i + len(assumes) for i in line.assumptions]))
            else:
                lines.append(line)
    else:
        lines = list(proof.lines)
    for i in range(len(rule.assumptions)):
        lines.append(Proof.Line(lines[len(lines) - 1].formula.second, MP, [i, len(lines) - 1]))
    return Proof(rule, AXIOMATIC_SYSTEM, lines)


def model_or_inconsistency(formulas: Sequence[Formula]) -> Union[Model, Proof]:
    """Either finds a model in which all the given formulas hold, or proves
    ``'~(p->p)'`` from these formulas.

    Parameters:
        formulas: formulas that use only the operators ``'->'`` and ``'~'``, to
            either find a model for or prove ``'~(p->p)'`` from.

    Returns:
        A model in which all of the given formulas hold if such exists,
        otherwise a valid proof of ``'~(p->p)'`` from the given formulas via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    for formula in formulas:
        assert formula.operators().issubset({'->', '~'})
    # Task 6.5

    all_variables = set()
    for formula in formulas:
        all_variables = all_variables.union(formula.variables().difference(all_variables))
    models = all_models(list(all_variables))
    for model in models:
        flag = False
        for formula in formulas:
            if not evaluate(formula, model):
                flag = True
                break
        if not flag:
            return model
    rule = InferenceRule(formulas, Formula('~', I0.conclusion))
    proof = prove_sound_inference(rule)
    return Proof(rule, AXIOMATIC_SYSTEM, proof.lines)


def prove_in_model_full(formula: Formula, model: Model) -> Proof:
    """Either proves the given formula or proves its negation, from the formulas
    that capture the given model.

    Parameters:
        formula: formula that contains no operators beyond ``'->'``, ``'~'``,
            ``'&'``, and ``'|'`` (and may contain constants), whose affirmation
            or negation is to prove.
        model: model from whose formulas to prove.

    Returns:
        If the given formula evaluates to ``True`` in the given model, then
        a valid proof of the formula; otherwise a valid proof of
        ``'~``\ `formula`\ ``'``. The returned proof is from the formulas that
        capture the given model, in the order returned by
        `formulas_capturing_model`\ ``(``\ `model`\ ``)``, via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM_FULL`.

    Examples:
        >>> proof = prove_in_model_full(Formula.parse('(p&q7)'),
        ...                             {'q7': False, 'p': True})
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        ~(p&q7)
        >>> proof.statement.assumptions
        (p, ~q7)
        >>> proof.rules == AXIOMATIC_SYSTEM_FULL
        True

        >>> proof = prove_in_model_full(Formula.parse('(p&q7)'),
        ...                             {'q7': True, 'p': True})
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        (p&q7)
        >>> proof.statement.assumptions
        (p, q7)
        >>> proof.rules == AXIOMATIC_SYSTEM_FULL
        True
    """
    assert formula.operators().issubset({'T', 'F', '->', '~', '&', '|'})
    assert is_model(model)
    # Optional Task 6.6
