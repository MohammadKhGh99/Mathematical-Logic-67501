# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: propositions/deduction.py

"""Useful proof manipulation maneuvers in Propositional Logic."""

from propositions.syntax import *
from propositions.proofs import *
from propositions.axiomatic_systems import *


def prove_corollary(antecedent_proof: Proof, consequent: Formula, conditional: InferenceRule) -> Proof:
    """Converts the given proof of a formula `antecedent` to a proof of the
    given formula `consequent` by using the given assumptionless inference rule
    of which ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
    specialization.

    Parameters:
        antecedent_proof: valid proof of `antecedent`.
        consequent: formula to prove.
        conditional: assumptionless inference rule of which the assumptionless
            inference rule with conclusion
            ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
            specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proof, via the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP` and `conditional`.
    """
    assert antecedent_proof.is_valid()
    assert InferenceRule([], Formula('->', antecedent_proof.statement.conclusion,
                                     consequent)).is_specialization_of(conditional)
    # Task 5.3a

    statement = InferenceRule(antecedent_proof.statement.assumptions, consequent)
    temp_formula = Formula("->", antecedent_proof.statement.conclusion, consequent)
    special_map = InferenceRule.get_formula_specialization(conditional.conclusion, temp_formula)
    temp_line = Proof.Line(conditional.specialize(special_map).conclusion, conditional, [])
    lines = list(antecedent_proof.lines) + [temp_line]
    n = len(lines)
    special_rule = InferenceRule([lines[n - 2].formula, lines[n - 1].formula], lines[n - 1].formula.second)
    special_map = MP.specialization_map(special_rule)
    lines.append(Proof.Line(MP.specialize(special_map).conclusion, MP, [len(lines) - 2, len(lines) - 1]))
    return Proof(statement, antecedent_proof.rules.union({MP, conditional}), lines)


def combine_proofs(antecedent1_proof: Proof, antecedent2_proof: Proof,
                   consequent: Formula, double_conditional: InferenceRule) -> \
        Proof:
    """Combines the given proofs of two formulas `antecedent1` and `antecedent2`
    into a proof of the given formula `consequent` by using the given
    assumptionless inference rule of which
    ``'(``\ `antecedent1`\ ``->(``\ `antecedent2`\ ``->``\ `consequent`\ ``))'``
    is a specialization.

    Parameters:
        antecedent1_proof: valid proof of `antecedent1`.
        antecedent2_proof: valid proof of `antecedent2` from the same
            assumptions and inference rules as `antecedent1_proof`.
        consequent: formula to prove.
        double_conditional: assumptionless inference rule of which the
            assumptionless inference rule with conclusion
            ``'(``\ `antecedent1`\ ``->(``\ `antecedent2`\ ``->``\ `consequent`\ ``))'``
            is a specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and `conditional`.
    """
    assert antecedent1_proof.is_valid()
    assert antecedent2_proof.is_valid()
    assert antecedent1_proof.statement.assumptions == \
           antecedent2_proof.statement.assumptions
    assert antecedent1_proof.rules == antecedent2_proof.rules
    assert InferenceRule(
        [], Formula('->', antecedent1_proof.statement.conclusion,
                    Formula('->', antecedent2_proof.statement.conclusion, consequent))
    ).is_specialization_of(double_conditional)
    # Task 5.3b

    statement = InferenceRule(antecedent1_proof.statement.assumptions, consequent)
    second_formula = Formula("->", antecedent2_proof.statement.conclusion, consequent)
    all_formula = Formula("->", antecedent1_proof.statement.conclusion, second_formula)
    specialized_map = double_conditional.specialization_map(InferenceRule([], all_formula))
    consequence = double_conditional.specialize(specialized_map).conclusion.second
    temp_proof = prove_corollary(antecedent1_proof, consequence, double_conditional)
    lines = list(temp_proof.lines)
    rules = antecedent1_proof.rules.union({MP})

    length_before = len(lines)
    for line in antecedent2_proof.lines:
        temp = list()
        if not line.is_assumption() and len(line.assumptions) > 0:
            for i in line.assumptions:
                temp.append(i + length_before)
            lines.append(Proof.Line(line.formula, line.rule, temp))
        else:
            lines.append(line)
    lines.append(Proof.Line(consequent, MP, [len(lines) - 1, len(temp_proof.lines) - 1]))

    flag = False
    for rule in rules:
        if not double_conditional.is_specialization_of(rule):
            flag = False
        else:
            flag = True
            i = 0
            while i < len(lines):
                if lines[i].rule == double_conditional:
                    lines = lines[:i] + [Proof.Line(lines[i].formula, rule, lines[i].assumptions)] + lines[i + 1:]
                i += 1
            break
    if not flag:
        rules = rules.union({double_conditional})
    return Proof(statement, rules, lines)


def _find_first_appearance(lines, last_assumption, proof, line, f):
    for i in range(len(lines) - 1, -1, -1):
        if lines[i].formula == Formula("->", last_assumption, proof.lines[line.assumptions[f]].formula):
            return i


def remove_assumption(proof: Proof) -> Proof:
    """Converts the given proof of some `conclusion` formula, the last
    assumption of which is an assumption `assumption`, to a proof of
    ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` from the same assumptions
    except `assumption`.

    Parameters:
        proof: valid proof to convert, with at least one assumption, via some
            set of inference rules all of which have no assumptions except
            perhaps `~propositions.axiomatic_systems.MP`.

    Returns:
        A valid proof of ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'``
        from the same assumptions as the given proof except the last one, via
        the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`, and
        `~propositions.axiomatic_systems.D`.
    """
    assert proof.is_valid()
    assert len(proof.statement.assumptions) > 0
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    # Task 5.4

    assumptions = proof.statement.assumptions[:-1]
    last_assumption = proof.statement.assumptions[-1]
    last_formula = Formula("->", last_assumption, proof.statement.conclusion)
    statement = InferenceRule(assumptions, last_formula)
    rules = proof.rules.union({I1, I0, MP, D})
    temp_lines = list()
    ind = -1
    for line in proof.lines:
        if line.formula in assumptions:
            temp_lines.append(Proof.Line(line.formula))
            temp_formula = Formula("->", line.formula, Formula("->", last_assumption, line.formula))
            temp_lines.append(Proof.Line(temp_formula, I1, []))
            ind += 2
            temp_lines.append(Proof.Line(Formula("->", last_assumption, line.formula), MP, [ind - 1, ind]))
            ind += 1
        elif line.formula == last_assumption:
            temp_lines.append(Proof.Line(Formula("->", last_assumption, line.formula), I0, []))
            ind += 1
        elif line.rule == MP and len(line.assumptions) == 2:
            i1 = _find_first_appearance(temp_lines, last_assumption, proof, line, 0)
            i2 = _find_first_appearance(temp_lines, last_assumption, proof, line, 1)
            substitute_map = {'p': last_assumption, 'q': proof.lines[line.assumptions[0]].formula, 'r': line.formula}
            temp = D.conclusion.substitute_variables(substitute_map)
            temp_lines.append(Proof.Line(temp, D, []))
            temp_lines.append(Proof.Line(temp.second, MP, [i2, len(temp_lines) - 1]))
            temp_lines.append(Proof.Line(temp.second.second, MP, [i1, len(temp_lines) - 1]))
            ind += 3
        elif line.rule in proof.rules:
            temp_lines.append(line)
            temp_formula = Formula("->", line.formula, Formula("->", last_assumption, line.formula))
            temp_lines.append(Proof.Line(temp_formula, I1, []))
            ind += 2
            temp_lines.append(Proof.Line(Formula("->", last_assumption, line.formula), MP, [ind - 1, ind]))
            ind += 1

    return Proof(statement, rules, temp_lines)


def prove_from_opposites(proof_of_affirmation: Proof,
                         proof_of_negation: Proof, conclusion: Formula) -> \
        Proof:
    """Combines the given proofs of a formula `affirmation` and its negation
    ``'~``\ `affirmation`\ ``'`` into a proof of the given formula.

    Parameters:
        proof_of_affirmation: valid proof of `affirmation`.
        proof_of_negation: valid proof of ``'~``\ `affirmation`\ ``'`` from the
            same assumptions and inference rules of `proof_of_affirmation`.

    Returns:
        A valid proof of `conclusion` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and
        `~propositions.axiomatic_systems.I2`.
    """
    assert proof_of_affirmation.is_valid()
    assert proof_of_negation.is_valid()
    assert proof_of_affirmation.statement.assumptions == \
           proof_of_negation.statement.assumptions
    assert Formula('~', proof_of_affirmation.statement.conclusion) == \
           proof_of_negation.statement.conclusion
    assert proof_of_affirmation.rules == proof_of_negation.rules
    # Task 5.6

    proof = combine_proofs(proof_of_negation, proof_of_affirmation, conclusion, I2)
    return Proof(InferenceRule(proof_of_affirmation.statement.assumptions, conclusion), proof.rules, proof.lines)


def prove_by_way_of_contradiction(proof: Proof) -> Proof:
    """Converts the given proof of ``'~(p->p)'``, the last assumption of which
    is an assumption ``'~``\ `formula`\ ``'``, to a proof of `formula` from the
    same assumptions except ``'~``\ `formula`\ ``'``.

    Parameters:
        proof: valid proof of ``'~(p->p)'`` to convert, the last assumption of
            which is of the form ``'~``\ `formula`\ ``'``, via some set of
            inference rules all of which have no assumptions except perhaps
            `~propositions.axiomatic_systems.MP`.

    Returns:
        A valid proof of `formula` from the same assumptions as the given proof
        except the last one, via the same inference rules as the given proof and
        in addition `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    assert proof.is_valid()
    assert proof.statement.conclusion == Formula.parse('~(p->p)')
    assert len(proof.statement.assumptions) > 0
    assert proof.statement.assumptions[-1].root == '~'
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    # Task 5.7

    new_proof = remove_assumption(proof)
    rules = new_proof.rules.union({MP, I1, I0, D, N})
    statement = InferenceRule(new_proof.statement.assumptions, proof.statement.assumptions[-1].first)
    lines = list(new_proof.lines)
    dic = {'p': proof.statement.conclusion.first, 'q': proof.statement.assumptions[-1].first}
    length = len(lines)
    modified = N.conclusion.substitute_variables(dic)
    lines += [Proof.Line(modified, N, []), Proof.Line(I0.conclusion, I0, [])]
    lines += [Proof.Line(modified.second, MP, [length - 1, length]), Proof.Line(dic['q'], MP, [length + 1, length + 2])]

    return Proof(statement, rules, lines)
