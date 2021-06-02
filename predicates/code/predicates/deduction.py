# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: predicates/deduction.py

"""Useful proof manipulation maneuvers in Predicate Logic."""

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *


def _find_first_appearance(lines, assumption, proof, f):
    # for i in range(len(lines)):
    for i in range(len(lines) - 1, -1, -1):
        if lines[i].formula == Formula("->", assumption, proof.lines[f].formula):
            return i


def remove_assumption(proof: Proof, assumption: Formula, print_as_proof_forms: bool = False) -> Proof:
    """Converts the given proof of some `conclusion` formula, an assumption of
    which is `assumption`, to a proof of
    ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` from the same assumptions
    except `assumption`.

    Parameters:
        proof: valid proof to convert, from assumptions/axioms that include
            `~predicates.prover.Prover.AXIOMS`.
        assumption: formula that is a simple assumption (i.e., without any
            templates) of the given proof, such that no line of the given proof
            is a UG line over a variable that is free in this assumption.

    Returns:
        A valid proof of ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'``
        from the same assumptions/axioms as the given proof except `assumption`.
    """
    assert proof.is_valid()
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions.issuperset(Prover.AXIOMS)
    for line in proof.lines:
        if isinstance(line, Proof.UGLine):
            assert line.formula.variable not in assumption.free_variables()
    # Task 11.1

    assumptions = proof.assumptions.difference({Schema(assumption)})
    prover = Prover(assumptions)

    for i, line in enumerate(proof.lines):
        if line.formula == assumption:
            prover.add_tautology(Formula('->', assumption, line.formula))
        elif isinstance(line, Proof.AssumptionLine):
            antecedent = prover.add_instantiated_assumption(line.formula, line.assumption, line.instantiation_map)
            formula = Formula('->', line.formula, Formula('->', assumption, line.formula))
            conditional = prover.add_tautological_implication(formula, {antecedent})
            prover.add_mp(Formula('->', assumption, line.formula), antecedent, conditional)
        elif isinstance(line, Proof.TautologyLine):
            prover.add_tautology(Formula('->', assumption, line.formula))
        elif isinstance(line, Proof.MPLine):
            i1 = _find_first_appearance(prover._lines, assumption, proof, line.antecedent_line_number)
            i2 = _find_first_appearance(prover._lines, assumption, proof, line.conditional_line_number)
            prover.add_tautological_implication(Formula('->', assumption, line.formula), {i1, i2})
        elif isinstance(line, Proof.UGLine):
            predicate = line.formula.predicate
            j = line.predicate_line_number
            new_i = _find_first_appearance(prover._lines, assumption, proof, j)
            v = line.formula.variable
            line1 = prover.add_ug(Formula('A', v, Formula('->', assumption, predicate)), new_i)
            first = Formula('A', v, Formula('->', assumption, predicate))
            second = Formula('->', assumption, line.formula)
            sub_map = {'Q': assumption, 'R': predicate.substitute({v: Term('_')}), 'x': v}
            line2 = prover.add_instantiated_assumption(Formula('->', first, second), Prover.US, sub_map)
            prover.add_mp(Formula('->', assumption, line.formula), line1, line2)
    return prover.qed()


def proof_by_way_of_contradiction(proof: Proof, assumption: Formula, print_as_proof_forms: bool = False) -> Proof:
    """Converts the given proof of a contradiction, an assumption of which is
    `assumption`, to a proof of ``'~``\ `assumption`\ ``'`` from the same
    assumptions except `assumption`.

    Parameters:
        proof: valid proof of a contradiction (i.e., a formula whose negation is
            a tautology) to convert, from assumptions/axioms that include
            `~predicates.prover.Prover.AXIOMS`.
        assumption: formula that is a simple assumption (i.e., without any
            templates) of the given proof, such that no line of the given proof
            is a UG line over a variable that is free in this assumption.

    Returns:
        A valid proof of ``'~``\ `assumption`\ ``'`` from the same
        assumptions/axioms as the given proof except `assumption`.
    """
    assert proof.is_valid()
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions.issuperset(Prover.AXIOMS)
    for line in proof.lines:
        if isinstance(line, Proof.UGLine):
            assert line.formula.variable not in assumption.free_variables()
    # Task 11.2

    assumptions = proof.assumptions.difference({Schema(assumption)})
    prover = Prover(assumptions)
    adding = prover.add_proof(Formula('->', assumption, proof.conclusion), remove_assumption(proof, assumption))
    prover.add_tautological_implication(Formula('~', assumption), {adding})
    return prover.qed()
