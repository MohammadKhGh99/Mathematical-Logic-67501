# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: predicates/prenex.py

"""Conversion of predicate-logic formulas into prenex normal form."""

from typing import Tuple

from logic_utils import fresh_variable_name_generator

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *

#: Additional axioms of quantification for Predicate Logic.
ADDITIONAL_QUANTIFICATION_AXIOMS = (
    Schema(Formula.parse('((~Ax[R(x)]->Ex[~R(x)])&(Ex[~R(x)]->~Ax[R(x)]))'),
           {'x', 'R'}),
    Schema(Formula.parse('((~Ex[R(x)]->Ax[~R(x)])&(Ax[~R(x)]->~Ex[R(x)]))'),
           {'x', 'R'}),
    Schema(Formula.parse('(((Ax[R(x)]&Q())->Ax[(R(x)&Q())])&'
                         '(Ax[(R(x)&Q())]->(Ax[R(x)]&Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Ex[R(x)]&Q())->Ex[(R(x)&Q())])&'
                         '(Ex[(R(x)&Q())]->(Ex[R(x)]&Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()&Ax[R(x)])->Ax[(Q()&R(x))])&'
                         '(Ax[(Q()&R(x))]->(Q()&Ax[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()&Ex[R(x)])->Ex[(Q()&R(x))])&'
                         '(Ex[(Q()&R(x))]->(Q()&Ex[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Ax[R(x)]|Q())->Ax[(R(x)|Q())])&'
                         '(Ax[(R(x)|Q())]->(Ax[R(x)]|Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Ex[R(x)]|Q())->Ex[(R(x)|Q())])&'
                         '(Ex[(R(x)|Q())]->(Ex[R(x)]|Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()|Ax[R(x)])->Ax[(Q()|R(x))])&'
                         '(Ax[(Q()|R(x))]->(Q()|Ax[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()|Ex[R(x)])->Ex[(Q()|R(x))])&'
                         '(Ex[(Q()|R(x))]->(Q()|Ex[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Ax[R(x)]->Q())->Ex[(R(x)->Q())])&'
                         '(Ex[(R(x)->Q())]->(Ax[R(x)]->Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Ex[R(x)]->Q())->Ax[(R(x)->Q())])&'
                         '(Ax[(R(x)->Q())]->(Ex[R(x)]->Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()->Ax[R(x)])->Ax[(Q()->R(x))])&'
                         '(Ax[(Q()->R(x))]->(Q()->Ax[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()->Ex[R(x)])->Ex[(Q()->R(x))])&'
                         '(Ex[(Q()->R(x))]->(Q()->Ex[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
                         '((Ax[R(x)]->Ay[Q(y)])&(Ay[Q(y)]->Ax[R(x)])))'),
           {'x', 'y', 'R', 'Q'}),
    Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
                         '((Ex[R(x)]->Ey[Q(y)])&(Ey[Q(y)]->Ex[R(x)])))'),
           {'x', 'y', 'R', 'Q'}))

E = 15
A = 14


def is_quantifier_free(formula: Formula) -> bool:
    """Checks if the given formula contains any quantifiers.

    Parameters:
        formula: formula to check.

    Returns:
        ``False`` if the given formula contains any quantifiers, ``True``
        otherwise.
    """
    # Task 11.3.1

    if is_equality(formula.root) or is_relation(formula.root):
        return True
    elif is_unary(formula.root):
        return is_quantifier_free(formula.first)
    elif is_binary(formula.root):
        return is_quantifier_free(formula.first) & is_quantifier_free(formula.second)
    elif is_quantifier(formula.root):
        return False


def is_in_prenex_normal_form(formula: Formula) -> bool:
    """Checks if the given formula is in prenex normal form.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula in prenex normal form, ``False``
        otherwise.
    """
    # Task 11.3.2

    if is_quantifier_free(formula):
        return True
    else:
        if is_quantifier(formula.root):
            return is_in_prenex_normal_form(formula.predicate)
        else:
            return False


def equivalence_of(formula1: Formula, formula2: Formula) -> Formula:
    """States the equivalence of the two given formulas as a formula.

    Parameters:
        formula1: first of the formulas the equivalence of which is to be
            stated.
        formula2: second of the formulas the equivalence of which is to be
            stated.

    Returns:
        The formula ``'((``\ `formula1`\ ``->``\ `formula2`\ ``)&(``\ `formula2`\ ``->``\ `formula1`\ ``))'``.
    """
    return Formula('&', Formula('->', formula1, formula2),
                   Formula('->', formula2, formula1))


def has_uniquely_named_variables(formula: Formula) -> bool:
    """Checks if the given formula has uniquely named variables.

    Parameters:
        formula: formula to check.

    Returns:
        ``False`` if in the given formula some variable name has both quantified
        and free occurrences or is quantified by more than one quantifier,
        ``True`` otherwise.

    Examples:
        >>> has_uniquely_named_variables(
        ...     Formula.parse('(x=0&(Ax[R(x)]|Ex[R(x)]))'))
        False
        >>> has_uniquely_named_variables(
        ...     Formula.parse('(x=0&(Ax[R(x)]|Ey[R(y)]))'))
        False
        >>> has_uniquely_named_variables(
        ...     Formula.parse('(y=0&(Ax[R(x)]|Ex[R(x)]))'))
        False
        >>> has_uniquely_named_variables(
        ...     Formula.parse('(x=0&(Ay[R(y)]|Ez[R(z)]))'))
        True
    """
    forbidden_variables = set(formula.free_variables())

    def has_uniquely_named_variables_helper(formula: Formula) -> bool:
        if is_unary(formula.root):
            return has_uniquely_named_variables_helper(formula.first)
        elif is_binary(formula.root):
            return has_uniquely_named_variables_helper(formula.first) and \
                   has_uniquely_named_variables_helper(formula.second)
        elif is_quantifier(formula.root):
            if formula.variable in forbidden_variables:
                return False
            forbidden_variables.add(formula.variable)
            return has_uniquely_named_variables_helper(formula.predicate)
        else:
            assert is_relation(formula.root) or is_equality(formula.root)
            return True

    return has_uniquely_named_variables_helper(formula)


def _uniquely_rename_quantified_variables(formula: Formula) -> Tuple[Formula, Proof]:
    """Converts the given formula to an equivalent formula with uniquely named
    variables, and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, which contains no variable names starting
            with ``z``.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, with the exact same structure but with the additional
        property of having uniquely named variables, obtained by consistently
        replacing each variable name that is bound in the given formula with a
        new variable name obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``. The
        second element of the pair is a proof of the equivalence of the given
        formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('~(w=x|Aw[(Ex[(x=w&Aw[w=x])]->Ax[x=y])])')
        >>> returned_formula, proof = _uniquely_rename_quantified_variables(formula)
        >>> returned_formula
        ~(w=x|Az58[(Ez17[(z17=z58&Az4[z4=z17])]->Az32[z32=y])])
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    for variable in formula.variables():
        assert variable[0] != 'z'
    # Task 11.5

    forbidden_variables = set(formula.free_variables())

    def just_helper(formula: Formula, map: dict):
        if is_unary(formula.root):
            proof = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)
            first_formula, first_proof = just_helper(formula.first, map)
            formula_ans = Formula(formula.root, first_formula)
            equivalence = equivalence_of(formula, formula_ans)

            conclusion_added = proof.add_proof(first_proof.conclusion, first_proof)
            proof.add_tautological_implication(equivalence, {conclusion_added})
            return formula_ans, proof.qed()
        elif is_binary(formula.root):
            proof = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)
            first_formula, first_proof = just_helper(formula.first, map)
            second_formula, second_proof = just_helper(formula.second, map)
            formula_ans = Formula(formula.root, first_formula, second_formula)
            equivalence = equivalence_of(formula, formula_ans)

            conclusion_added_1 = proof.add_proof(first_proof.conclusion, first_proof)
            conclusion_added_2 = proof.add_proof(second_proof.conclusion, second_proof)
            proof.add_tautological_implication(equivalence, {conclusion_added_1, conclusion_added_2})
            return formula_ans, proof.qed()

        elif is_quantifier(formula.root):
            proof = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)
            quantifier_variable = next(fresh_variable_name_generator)
            map[formula.variable] = Term(quantifier_variable)
            predicate_formula, predicate_proof = just_helper(formula.predicate, {})
            sub_predicate_formula = predicate_formula.substitute(map)

            formula_ans = Formula(formula.root, quantifier_variable, sub_predicate_formula)
            equivalence_predicate = equivalence_of(formula.predicate, predicate_formula)
            equivalence_formula = equivalence_of(formula, formula_ans)
            equivalence = Formula("->", equivalence_predicate, equivalence_formula)

            conclusion_added = proof.add_proof(predicate_proof.conclusion, predicate_proof)
            root = E
            if formula.root == 'A':
                root = A

            original_predicate_substitute = formula.predicate.substitute({formula.variable: Term("_")})
            predicate_substitute = predicate_formula.substitute({formula.variable: Term("_")})

            instantiated_assumption = proof.add_instantiated_assumption(equivalence, ADDITIONAL_QUANTIFICATION_AXIOMS[root], {
            "R": original_predicate_substitute, "Q": predicate_substitute, "y": quantifier_variable, "x": formula.variable})
            proof.add_mp(equivalence_formula, conclusion_added, instantiated_assumption)

            return formula_ans, proof.qed()

        else:  # equality or relation
            proof = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)
            proof.add_tautology(equivalence_of(formula, formula))
            return formula, proof.qed()

    return just_helper(formula, {})


def unique_rename(formula):
    return _uniquely_rename_quantified_variables(formula)


def _pull_out_quantifications_across_negation(formula: Formula) -> Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'~``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_formula`\ ``]``...\ ``]]'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[~``\ `inner_formula`\ ``]``...\ ``]]'``,
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, whose root is a negation, i.e., which is of
            the form
            ``'~``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_formula`\ ``]``...\ ``]]'``
            where `n`>=0, each `Qi` is a quantifier, each `xi` is a variable
            name, and `inner_formula` does not start with a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[~``\ `inner_formula`\ ``]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the `xi` variable names and
        `inner_formula` are the same as in the given formula. The second element
        of the pair is a proof of the equivalence of the given formula and the
        returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('~Ax[Ey[R(x,y)]]')
        >>> returned_formula, proof = _pull_out_quantifications_across_negation(
        ...     formula)
        >>> returned_formula
        Ex[Ay[~R(x,y)]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert is_unary(formula.root)
    # Task 11.6

    formula_first = formula.first
    if is_quantifier(formula_first.root):
        root = E
        flip_root = 'A'
        axiom_num = 1
        if formula_first.root == 'A':
            root = A
            flip_root = 'E'
            axiom_num = 0

        proof = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)
        negate_predicate = Formula("~", formula_first.predicate)
        predicate_formula, predicate_proof = _pull_out_quantifications_across_negation(negate_predicate)

        # renames
        predicate_conclusion = predicate_proof.conclusion
        predicate_conclusion_first = predicate_conclusion.first
        formula_variable = formula_first.variable

        left_side_formula = Formula(flip_root, formula_variable, predicate_conclusion_first.first)
        formula_ans = Formula(flip_root, formula_variable, predicate_conclusion_first.second)
        equivalence = equivalence_of(left_side_formula, formula_ans)
        instantiated_assumption_answer = Formula("->", predicate_conclusion, equivalence)

        conclusion_added = proof.add_proof(predicate_conclusion, predicate_proof)

        # renames
        original_predicate_substitute = predicate_conclusion_first.first.substitute({formula_first.variable: Term("_")})
        predicate_substitute = predicate_conclusion_first.second.substitute({formula_first.variable: Term("_")})

        instantiated_assumption = proof.add_instantiated_assumption(instantiated_assumption_answer,
                                                                    ADDITIONAL_QUANTIFICATION_AXIOMS[root], {
                                                                        "R": original_predicate_substitute,
                                                                        "Q": predicate_substitute,
                                                                        "y": formula_variable, "x": formula_variable})
        MP_first = proof.add_mp(equivalence, conclusion_added, instantiated_assumption)
        # -------
        equivalence = equivalence_of(formula, left_side_formula)
        original_predicate_substitute = formula_first.predicate.substitute({formula_variable: Term("_")})
        instantiated_assumption = proof.add_instantiated_assumption(equivalence,
                                                                    ADDITIONAL_QUANTIFICATION_AXIOMS[axiom_num], {
                                                                        "R": original_predicate_substitute,
                                                                        "x": formula_variable})
        # -----
        equivalence = equivalence_of(formula, formula_ans)
        proof.add_tautological_implication(equivalence, {MP_first, instantiated_assumption})
        return formula_ans, proof.qed()

    else:
        proof = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)
        proof.add_tautology(equivalence_of(formula, formula))
        return formula, proof.qed()


def _pull_out_quantifications_from_left_across_binary_operator(formula: Formula) -> Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `second`\ ``)'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `inner_first`\ `*`\ `second`\ ``)]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `second`\ ``)'``
            where `*` is a binary operator, `n`>=0, each `Qi` is a quantifier,
            each `xi` is a variable name, and `inner_first` does not start with
            a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `inner_first`\ `*`\ `second`\ ``)]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the operator `*`, the `xi`
        variable names, `inner_first`, and `second` are the same as in the given
        formula. The second element of the pair is a proof of the equivalence of
        the given formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]&Ez[P(1,z)])')
        >>> returned_formula, proof = _pull_out_quantifications_from_left_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ax[Ey[(R(x,y)&Ez[P(1,z)])]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.7.1

    prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)
    to_return = None
    axiom_before = None
    temp = ADDITIONAL_QUANTIFICATION_AXIOMS
    if not is_quantifier(formula.first.root):
        prover.add_tautology(equivalence_of(formula, formula))
        to_return = formula
    else:
        root = None
        if formula.first.root == 'E':
            axiom_before = temp[7]
            axiom_before = temp[11] if formula.root == '->' else axiom_before
            axiom_before = temp[3] if formula.root == '&' else axiom_before  # todo
            root = 'E'
        else:
            axiom_before = temp[6]
            axiom_before = temp[10] if formula.root == '->' else axiom_before
            axiom_before = temp[2] if formula.root == '&' else axiom_before  # todo
            root = 'A'

        form = Formula(formula.root, formula.first.predicate, formula.second)
        left_formula, left_proof = _pull_out_quantifications_from_left_across_binary_operator(form)

        if (formula.root != '->' or root != 'A') and (formula.root == '->' or root != 'E'):
            axiom = temp[A]
            root = 'A'
        else:
            axiom = temp[E]
            root = 'E'

        to_return = Formula(root, formula.first.variable, left_proof.conclusion.first.second)
        form = Formula(root, formula.first.variable, left_proof.conclusion.first.first)
        eq_form = equivalence_of(form, to_return)
        antecedent = prover.add_proof(left_proof.conclusion, left_proof)

        replace_r = left_proof.conclusion.first.first.substitute({formula.first.variable: Term('_')})
        replace_q = left_proof.conclusion.first.second.substitute({formula.first.variable: Term('_')})
        spec_map = {'R': replace_r, 'Q': replace_q, 'x': formula.first.variable, 'y': formula.first.variable}
        conditional = prover.add_instantiated_assumption(Formula('->', left_proof.conclusion, eq_form), axiom, spec_map)

        mp = prover.add_mp(eq_form, antecedent, conditional)

        replace_r = formula.first.predicate.substitute({formula.first.variable: Term('_')})
        spec_map = {'R': replace_r, 'Q': formula.second, 'x': formula.first.variable}
        instantiation = prover.add_instantiated_assumption(equivalence_of(formula, form), axiom_before, spec_map)

        prover.add_tautological_implication(equivalence_of(formula, to_return), {mp, instantiation})
    return to_return, prover.qed()


def _pull_out_quantifications_from_right_across_binary_operator(formula: Formula) -> Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `first`\ `*`\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `first`\ `*`\ `inner_second`\ ``)]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `first`\ `*`\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
            where `*` is a binary operator, `n`>=0, each `Qi` is a quantifier,
            each `xi` is a variable name, and `inner_second` does not start with
            a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `first`\ `*`\ `inner_second`\ ``)]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the operator `*`, the `xi`
        variable names, `first`, and `inner_second` are the same as in the given
        formula. The second element of the pair is a proof of the equivalence of
        the given formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]|Ez[P(1,z)])')
        >>> returned_formula, proof = _pull_out_quantifications_from_right_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ez[(Ax[Ey[R(x,y)]]|P(1,z))]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.7.2

    prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)
    temp = ADDITIONAL_QUANTIFICATION_AXIOMS
    if not is_quantifier(formula.second.root):
        prover.add_tautology(equivalence_of(formula, formula))
        to_return = formula
    else:
        if formula.second.root == 'E':
            axiom_before = temp[9]
            axiom_before = temp[13] if formula.root == '->' else axiom_before
            axiom_before = temp[5] if formula.root == '&' else axiom_before  # todo
            axiom = temp[E]
            root = 'E'
        else:
            axiom_before = temp[8]
            axiom_before = temp[12] if formula.root == '->' else axiom_before
            axiom_before = temp[4] if formula.root == '&' else axiom_before  # todo
            axiom = temp[A]
            root = 'A'

        form = Formula(formula.root, formula.first, formula.second.predicate)
        right_formula, right_proof = _pull_out_quantifications_from_right_across_binary_operator(form)

        to_return = Formula(root, formula.second.variable, right_proof.conclusion.second.first)
        form = Formula(root, formula.second.variable, right_proof.conclusion.second.second)
        eq_form = equivalence_of(form, to_return)
        antecedent = prover.add_proof(right_proof.conclusion, right_proof)

        replace_r = right_proof.conclusion.second.second.substitute({formula.second.variable: Term('_')})
        replace_q = right_proof.conclusion.second.first.substitute({formula.second.variable: Term('_')})
        spec_map = {'R': replace_r, 'Q': replace_q, 'x': formula.second.variable, 'y': formula.second.variable}
        conditional = prover.add_instantiated_assumption(Formula('->', right_proof.conclusion, eq_form), axiom,
                                                         spec_map)

        mp = prover.add_mp(eq_form, antecedent, conditional)

        replace_r = formula.second.predicate.substitute({formula.second.variable: Term('_')})
        spec_map = {'R': replace_r, 'Q': formula.first, 'x': formula.second.variable}
        instantiation = prover.add_instantiated_assumption(equivalence_of(formula, form), axiom_before, spec_map)

        prover.add_tautological_implication(equivalence_of(formula, to_return), {mp, instantiation})
    return to_return, prover.qed()


def _pull_out_quantifications_across_binary_operator(formula: Formula) -> Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `P1`\ `y1`\ ``[``\ `P2`\ `y2`\ ``[``...\ `Pm`\ `ym`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[``\ `P'1`\ `y1`\ ``[``\ `P'2`\ `y2`\ ``[``...\ `P'm`\ `ym`\ ``[(``\ `inner_first`\ `*`\ `inner_second`\ ``)]``...\ ``]]]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `P1`\ `y1`\ ``[``\ `P2`\ `y2`\ ``[``...\ `Pm`\ `ym`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
            where `*` is a binary operator, `n`>=0, `m`>=0, each `Qi` and `Pi`
            is a quantifier, each `xi` and `yi` is a variable name, and neither
            `inner_first` nor `inner_second` starts with a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[``\ `P'1`\ `y1`\ ``[``\ `P'2`\ `y2`\ ``[``...\ `P'm`\ `ym`\ ``[(``\ `inner_first`\ `*`\ `inner_second`\ ``)]``...\ ``]]]``...\ ``]]'``
        where each `Q'i` and `P'i` is a quantifier, and where the operator `*`,
        the `xi` and `yi` variable names, `inner_first`, and `inner_second` are
        the same as in the given formula. The second element of the pair is a
        proof of the equivalence of the given formula and the returned formula
        (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]->Ez[P(1,z)])')
        >>> returned_formula, proof = _pull_out_quantifications_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ex[Ay[Ez[(R(x,y)->P(1,z))]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.8

    proof = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)
    temp = ADDITIONAL_QUANTIFICATION_AXIOMS

    left_formula, left_proof = _pull_out_quantifications_from_left_across_binary_operator(formula)
    left_conclusion = proof.add_proof(left_proof.conclusion, left_proof)

    after_all_quantifiers = left_formula
    while is_quantifier(after_all_quantifiers.root):
        after_all_quantifiers = after_all_quantifiers.predicate

    right_formula, right_proof = _pull_out_quantifications_from_right_across_binary_operator(after_all_quantifiers)
    right_conclusion = proof.add_proof(right_proof.conclusion, right_proof)

    def helper(main_formula, last_line, formula1, formula2):
        def check_equivalence(main_formula, last_line, formula1, formula2):
            axiom = temp[A]
            if main_formula.root == "E":
                axiom = temp[E]

            if is_quantifier(main_formula.root):
                last_line, formula1, formula2 = check_equivalence(main_formula.predicate, last_line, formula1, formula2)

                new_formula1 = Formula(main_formula.root, main_formula.variable, formula1)
                new_formula2 = Formula(main_formula.root, main_formula.variable, formula2)

                equivalence_old = equivalence_of(formula1, formula2)
                equivalence_new = equivalence_of(new_formula1, new_formula2)
                equivalence_inside = Formula("->", equivalence_old, equivalence_new)
                # renames
                replace_r = formula1.substitute({main_formula.variable: Term("_")})
                replace_q = formula2.substitute({main_formula.variable: Term("_")})

                spec_map = {"R": replace_r, "Q": replace_q, "y": main_formula.variable, "x": main_formula.variable}
                instantiated = proof.add_instantiated_assumption(equivalence_inside, axiom, spec_map)
                last_line = proof.add_mp(equivalence_new, last_line, instantiated)
                return last_line, new_formula1, new_formula2

            else:
                return last_line, formula1, formula2

        last_step, formula1, formula2 = check_equivalence(main_formula, last_line, formula1, formula2)
        return last_step, formula2

    rpcff = right_proof.conclusion.first.first
    rpcfs = right_proof.conclusion.first.second

    last_line, to_return = helper(left_formula, right_conclusion, rpcff, rpcfs)
    equivalence = equivalence_of(formula, to_return)
    proof.add_tautological_implication(equivalence, {left_conclusion, last_line})
    return to_return, proof.qed()


def _to_prenex_normal_form_from_uniquely_named_variables(formula: Formula) -> Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables to an equivalent
    formula in prenex normal form, and proves the equivalence of these two
    formulas.

    Parameters:
        formula: formula with uniquely named variables to convert.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but in prenex normal form. The second element of the pair
        is a proof of the equivalence of the given formula and the returned
        formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(~(Ax[Ey[R(x,y)]]->Ez[P(1,z)])|S(w))')
        >>> returned_formula, proof = _to_prenex_normal_form_from_uniquely_named_variables(
        ...     formula)
        >>> returned_formula
        Ax[Ey[Az[(~(R(x,y)->P(1,z))|S(w))]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    # Task 11.9

    temp = ADDITIONAL_QUANTIFICATION_AXIOMS
    prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)
    to_return = None
    if is_equality(formula.root):
        prover.add_tautology(equivalence_of(formula, formula))
        to_return = formula
    elif is_unary(formula.root):
        first_formula, first_proof = _to_prenex_normal_form_from_uniquely_named_variables(formula.first)
        adding_proof1 = prover.add_proof(first_proof.conclusion, first_proof)
        unary_formula, unary_proof = _pull_out_quantifications_across_negation(Formula(formula.root, first_formula))
        adding_proof2 = prover.add_proof(unary_proof.conclusion, unary_proof)
        prover.add_tautological_implication(equivalence_of(formula, unary_formula), {adding_proof1, adding_proof2})
        to_return = unary_formula
    elif is_binary(formula.root):
        first_formula, first_proof = _to_prenex_normal_form_from_uniquely_named_variables(formula.first)
        second_formula, second_proof = _to_prenex_normal_form_from_uniquely_named_variables(formula.second)
        adding_proof1 = prover.add_proof(first_proof.conclusion, first_proof)
        adding_proof2 = prover.add_proof(second_proof.conclusion, second_proof)
        to_pull = Formula(formula.root, first_formula, second_formula)
        binary_formula, binary_proof = _pull_out_quantifications_across_binary_operator(to_pull)
        adding_proof3 = prover.add_proof(binary_proof.conclusion, binary_proof)
        lines_numbers = {adding_proof1, adding_proof2, adding_proof3}
        prover.add_tautological_implication(equivalence_of(formula, binary_formula), lines_numbers)
        to_return = binary_formula
    elif is_quantifier(formula.root):
        predicate_formula, predicate_proof = _to_prenex_normal_form_from_uniquely_named_variables(formula.predicate)
        adding_proof = prover.add_proof(predicate_proof.conclusion, predicate_proof)
        to_return = Formula(formula.root, formula.variable, predicate_formula)
        second = equivalence_of(formula, to_return)
        instantiated_formula = Formula('->', equivalence_of(formula.predicate, predicate_formula), second)
        replace_r = formula.predicate.substitute({formula.variable: Term('_')})
        replace_q = predicate_formula.substitute({formula.variable: Term('_')})
        instantiate_map = {'R': replace_r, 'Q': replace_q, 'x': formula.variable, 'y': formula.variable}
        axiom = temp[E] if formula.root == 'E' else temp[A]
        adding_instantiated = prover.add_instantiated_assumption(instantiated_formula, axiom, instantiate_map)
        prover.add_mp(second, adding_proof, adding_instantiated)
    else:
        prover.add_tautology(equivalence_of(formula, formula))
        to_return = formula
    return to_return, prover.qed()


def to_prenex(formula):
    return _to_prenex_normal_form_from_uniquely_named_variables(formula)


def to_prenex_normal_form(formula: Formula) -> Tuple[Formula, Proof]:
    """Converts the given formula to an equivalent formula in prenex normal
    form, and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, which contains no variable names starting
            with ``z``.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but in prenex normal form. The second element of the pair
        is a proof of the equivalence of the given formula and the returned
        formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('~(w=x|Aw[(Ex[(x=w&Aw[w=x])]->Ax[x=y])])')
        >>> returned_formula, proof = to_prenex_normal_form(formula)
        >>> returned_formula
        Ez58[Ez17[Az4[Ez32[~(w=x|((z17=z58&z4=z17)->z32=y))]]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    for variable in formula.variables():
        assert variable[0] != 'z'
    # Task 11.10

    prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)
    unique_formula, unique_proof = _uniquely_rename_quantified_variables(formula)
    normal_formula, normal_proof = _to_prenex_normal_form_from_uniquely_named_variables(unique_formula)
    adding_proof1 = prover.add_proof(unique_proof.conclusion, unique_proof)
    adding_proof2 = prover.add_proof(normal_proof.conclusion, normal_proof)
    prover.add_tautological_implication(equivalence_of(formula, normal_formula), {adding_proof1, adding_proof2})
    return normal_formula, prover.qed()
