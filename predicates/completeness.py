# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: predicates/completeness.py

"""Building blocks for proving the Completeness Theorem for Predicate Logic."""

from typing import AbstractSet, Container, Set, Union

from logic_utils import fresh_constant_name_generator

from predicates.syntax import *
from predicates.semantics import *
from predicates.proofs import *
from predicates.prover import *
from predicates.deduction import *
from predicates.prenex import *
import itertools as it


def get_constants(formulas: AbstractSet[Formula]) -> Set[str]:
    """Finds all constant names in the given formulas.

    Parameters:
        formulas: formulas to find all constant names in.

    Returns:
        A set of all constant names used in one or more of the given formulas.
    """
    constants = set()
    for formula in formulas:
        constants.update(formula.constants())
    return constants


def is_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if the given set of sentences is primitively, universally, and
        existentially closed; ``False`` otherwise.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    return is_primitively_closed(sentences) and \
           is_universally_closed(sentences) and \
           is_existentially_closed(sentences)


def is_primitively_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is
    primitively closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if for every n-ary relation name from the given sentences, and
        for every n (not necessarily distinct) constant names from the given
        sentences, either the invocation of this relation name over these
        constant names (in order), or the negation of this invocation (or both),
        is one of the given sentences; ``False`` otherwise.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and len(sentence.free_variables()) == 0
    # Task 12.1.1
    temp = [relation for sentence in sentences for relation in sentence.relations()]
    length = temp[0][1]
    relation = temp[0][0]
    s = {Term(const) for const in get_constants(sentences)}
    combinations = list(it.product(s, repeat=length))
    if len(combinations) > len(sentences):
        return False
    for sentence in sentences:
        if is_unary(sentence.root):
            if str(sentence.first) == relation and sentence.first.arguments not in combinations:
                return False
        else:
            if str(sentence.root) == relation and sentence.arguments not in combinations:
                return False
    return True


def is_universally_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is
    universally closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if for every universally quantified sentence of the given
        sentences, and for every constant name from the given sentences, the
        predicate of this quantified sentence, with every free occurrence of the
        universal quantification variable replaced with this constant name, is
        one of the given sentences; ``False`` otherwise.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and len(sentence.free_variables()) == 0
    # Task 12.1.2

    s = {Term(const) for const in get_constants(sentences)}
    for sentence in sentences:
        if sentence.root == 'A':
            predicate = sentence.predicate
            for const in s:
                if predicate.substitute({sentence.variable: const}) not in sentences:
                    return False
    return True


def is_existentially_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is
    existentially closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if for every existentially quantified sentence of the given
        sentences there exists a constant name such that the predicate of this
        quantified sentence, with every free occurrence of the existential
        quantification variable replaced with this constant name, is one of the
        given sentences; ``False`` otherwise.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and len(sentence.free_variables()) == 0
    # Task 12.1.3

    s = {Term(const) for const in get_constants(sentences)}
    counter = 0
    quantified_counter = 0
    for sentence in sentences:
        if sentence.root == 'E':
            counter += 1
            predicate = sentence.predicate
            for const in s:
                if predicate.substitute({sentence.variable: const}) in sentences:
                    quantified_counter += 1
                    break
    if quantified_counter == counter:
        return True
    return False


def find_unsatisfied_quantifier_free_sentence(sentences: Container[Formula],
                                              model: Model[str],
                                              unsatisfied: Formula) -> Formula:
    """
    Given a closed set of prenex-normal-form sentences, given a model whose
    universe is the set of all constant names from the given sentences, and
    given a sentence from the given set that the given model does not satisfy,
    finds a quantifier-free sentence from the given set that the given model
    does not satisfy.
    
    Parameters:
        sentences: closed set of prenex-normal-form sentences, which is only to
            be accessed using containment queries, i.e., using the ``in``
            operator as in:

            >>> if sentence in sentences:
            ...     print('contained!')

        model: model for all element names from the given sentences, whose
            universe is `get_constants`\ ``(``\ `sentences`\ ``)``.
        unsatisfied: sentence (which possibly contains quantifiers) from the
            given sentences that is not satisfied by the given model.

    Returns:
        A quantifier-free sentence from the given sentences that is not
        satisfied by the given model.
    """
    # We assume that every sentence in sentences is of type formula, is in
    # prenex normal form, and has no free variables, and furthermore that the
    # set of constants that appear somewhere in sentences is model.universe;
    # but we cannot assert these since we cannot iterate over sentences.
    for constant in model.universe:
        assert is_constant(constant)
    assert is_in_prenex_normal_form(unsatisfied)
    assert len(unsatisfied.free_variables()) == 0
    assert unsatisfied in sentences
    assert not model.evaluate_formula(unsatisfied)
    # Task 12.2

    consts = model.universe
    if is_quantifier(unsatisfied.root):
        for const in consts:
            cur = unsatisfied.predicate.substitute({unsatisfied.variable: Term.parse(const)})
            if cur in sentences and not model.evaluate_formula(cur):
                return find_unsatisfied_quantifier_free_sentence(sentences, model, cur)
    else:
        return unsatisfied


def get_primitives(quantifier_free: Formula) -> Set[Formula]:
    """Finds all primitive subformulas of the given quantifier-free formula.

    Parameters:
        quantifier_free: quantifier-free formula whose subformulas are to
            be searched.

    Returns:
        The primitive subformulas (i.e., relation invocations) of the given
        quantifier-free formula.

    Examples:
        The primitive subformulas of ``'(R(c1,d)|~(Q(c1)->~R(c2,a)))'`` are
        ``'R(c1,d)'``, ``'Q(c1)'``, and ``'R(c2,a)'``.
    """
    assert is_quantifier_free(quantifier_free)
    # Task 12.3.1

    primitives = set()
    if is_unary(quantifier_free.root):
        primitives = primitives.union(get_primitives(quantifier_free.first))
    elif is_binary(quantifier_free.root):
        primitives = primitives.union(get_primitives(quantifier_free.first))
        primitives = primitives.union(get_primitives(quantifier_free.second))
    elif is_relation(quantifier_free.root):
        primitives.update({quantifier_free})
    return primitives


def model_or_inconsistency(sentences: AbstractSet[Formula]) -> Union[Model[str], Proof]:
    """Either finds a model in which the given closed set of prenex-normal-form
    sentences holds, or proves a contradiction from these sentences.

    Parameters:
        sentences: closed set of prenex-normal-form sentences to either find a
            model for or prove a contradiction from.

    Returns:
        A model in which all of the given sentences hold if such exists,
        otherwise a valid proof of  a contradiction from the given formulas via
        `~predicates.prover.Prover.AXIOMS`.
    """
    assert is_closed(sentences)
    # Task 12.3.2

    universe = get_constants(sentences)
    relation_meanings = dict()
    constant_meanings = {const: const for const in list(universe)}
    for sentence in sentences:
        if is_relation(sentence.root):
            def to_str(arg):
                return str(arg)

            if sentence.root not in relation_meanings.keys():
                relation_meanings[sentence.root] = {tuple(map(to_str, sentence.arguments))}
            else:
                relation_meanings[sentence.root].update({tuple(map(to_str, sentence.arguments))})
    model = Model(universe, constant_meanings, relation_meanings)
    for sentence in sentences:
        if not model.evaluate_formula(sentence):
            unsatisfied = find_unsatisfied_quantifier_free_sentence(sentences, model, sentence)
            prover = Prover(sentences)
            primitives = list(get_primitives(unsatisfied))
            p = primitives[0] if primitives[0] in sentences else Formula('~', primitives[0])
            to_use = Formula('&', unsatisfied, p)
            line_numbers = {prover.add_assumption(p)}
            for prim in primitives:
                assume = prim if prim in sentences else Formula('~', prim)
                line_numbers.add(prover.add_assumption(assume))
                to_use = Formula('&', to_use, assume)
            line_numbers.add(prover.add_assumption(unsatisfied))
            prover.add_tautological_implication(to_use, line_numbers)
            return prover.qed()
    return model


def combine_contradictions(proof_from_affirmation: Proof,
                           proof_from_negation: Proof) -> Proof:
    """Combines the given two proofs of contradictions, both from the same
    assumptions/axioms except that the latter has an extra assumption that is
    the negation of an extra assumption that the former has, into a single proof
    of a contradiction from only the common assumptions/axioms.

    Parameters:
        proof_from_affirmation: valid proof of a contradiction from one or more
            assumptions/axioms that are all sentences and that include
            `~predicates.prover.Prover.AXIOMS`.
        proof_from_negation: valid proof of a contradiction from the same
            assumptions/axioms of `proof_from_affirmation`, but with one
            simple assumption `assumption` replaced with its negation
            ``'~``\ `assumption` ``'``.

    Returns:
        A valid proof of a contradiction from only the assumptions/axioms common
        to the given proofs (i.e., without `assumption` or its negation).
    """
    assert proof_from_affirmation.is_valid()
    assert proof_from_negation.is_valid()
    common_assumptions = proof_from_affirmation.assumptions.intersection(
        proof_from_negation.assumptions)
    assert len(common_assumptions) == len(proof_from_affirmation.assumptions) - 1
    assert len(common_assumptions) == len(proof_from_negation.assumptions) - 1
    affirmed_assumption = list(
        proof_from_affirmation.assumptions.difference(common_assumptions))[0]
    negated_assumption = list(proof_from_negation.assumptions.difference(common_assumptions))[0]
    assert len(affirmed_assumption.templates) == 0
    assert len(negated_assumption.templates) == 0
    assert negated_assumption.formula == Formula('~', affirmed_assumption.formula)
    assert proof_from_affirmation.assumptions.issuperset(Prover.AXIOMS)
    assert proof_from_negation.assumptions.issuperset(Prover.AXIOMS)
    for assumption in common_assumptions.union({affirmed_assumption, negated_assumption}):
        assert len(assumption.formula.free_variables()) == 0
    # Task 12.4

    assumptions = proof_from_affirmation.assumptions.intersection(proof_from_negation.assumptions)
    prover = Prover(assumptions)
    normal_extra = list(proof_from_affirmation.assumptions - assumptions)
    normal_contra = proof_by_way_of_contradiction(proof_from_affirmation, normal_extra[0].formula)
    line1 = prover.add_proof(normal_contra.conclusion, normal_contra)

    negation_extra = list(proof_from_negation.assumptions - assumptions)
    negation_contra = proof_by_way_of_contradiction(proof_from_negation, negation_extra[0].formula)
    line2 = prover.add_proof(negation_contra.conclusion, negation_contra)

    prover.add_tautological_implication(Formula('&', normal_contra.conclusion, negation_contra.conclusion),
                                        {line1, line2})
    return prover.qed()


def eliminate_universal_instantiation_assumption(proof: Proof, constant: str, instantiation: Formula,
                                                 universal: Formula) -> Proof:
    """Converts the given proof of a contradiction, whose assumptions/axioms
    include `universal` and `instantiation`, where the latter is a universal
    instantiation of the former, to a proof of a contradiction from the same
    assumptions without `instantiation`.

    Parameters:
        proof: valid proof of a contradiction from one or more
            assumptions/axioms that are all sentences and that include
            `~predicates.prover.Prover.AXIOMS`.
        constant:
        universal: assumption of the given proof that is universally quantified.
        instantiation: assumption of the given proof that is obtained from the
            predicate of `universal` by replacing all free occurrences of the
            universal quantification variable by some constant.

    Returns:
        A valid proof of a contradiction from the assumptions/axioms of the
        proof except `instantiation`.
    """
    assert proof.is_valid()
    assert is_constant(constant)
    assert Schema(instantiation) in proof.assumptions
    assert Schema(universal) in proof.assumptions
    assert universal.root == 'A'
    assert instantiation == universal.predicate.substitute({universal.variable: Term(constant)})
    for assumption in proof.assumptions:
        assert len(assumption.formula.free_variables()) == 0
    # Task 12.5

    assumptions = proof.assumptions - {Schema(instantiation)}
    prover = Prover(assumptions)
    contr_proof = proof_by_way_of_contradiction(proof, instantiation)
    line1 = prover.add_proof(contr_proof.conclusion, contr_proof)
    line2 = prover.add_assumption(universal)
    line3 = prover.add_universal_instantiation(instantiation, line2, Term(constant))
    prover.add_tautological_implication(Formula('&', contr_proof.conclusion, contr_proof.conclusion.first),
                                        {line1, line3})
    return prover.qed()


def universal_closure_step(sentences: AbstractSet[Formula]) -> Set[Formula]:
    """Augments the given sentences with all universal instantiations of each
    universally quantified sentence from these sentences, with respect to all
    constant names from these sentences.

    Parameters:
        sentences: prenex-normal-form sentences to augment with their universal
            instantiations.

    Returns:
        A set of all of the given sentences, and in addition any formula that
        can be obtained replacing in the predicate of any universally quantified
        sentence from the given sentences, all occurrences of the quantification
        variable with some constant from the given sentences.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    # Task 12.6
    new_sen = set()
    new_sen.update(sentences)
    s = get_constants(sentences)
    for sentence in sentences:
        if sentence.root == 'A':
            predicate = sentence.predicate
            for const in s:
                new_sen.add(predicate.substitute({sentence.variable: Term(const)}))

    return new_sen


def replace_constant(proof: Proof, constant: str, variable: str = 'zz') -> \
        Proof:
    """Replaces all occurrences of the given constant in the given proof with
    the given variable.

    Parameters:
        proof: valid proof in which to replace.
        constant: constant name that does not appear as a template constant name
            in any of the assumptions of the given proof.
        variable: variable name that does not appear anywhere in given the proof
            or in its assumptions.

    Returns:
        A valid proof where every occurrence of the given constant name in the
        given proof and in its assumptions is replaced with the given variable
        name.
    """
    assert proof.is_valid()
    assert is_constant(constant)
    assert is_variable(variable)
    for assumption in proof.assumptions:
        assert constant not in assumption.templates
        assert variable not in assumption.formula.variables()
    for line in proof.lines:
        assert variable not in line.formula.variables()
    # Task 12.7.1

    new_proof_conc = proof.conclusion.substitute({constant: Term(variable)})
    new_proof_ass = set()
    for ass in proof.assumptions:
        new_proof_ass.add(_helper_for_ass(constant, variable, ass))

    new_proof_lines = []
    for line in proof.lines:
        if constant in line.formula.constants():
            if isinstance(line, Proof.AssumptionLine):
                new_formula = line.formula.substitute({constant: Term(variable)})
                new_ass = _helper_for_ass(constant, variable, line.assumption)

                new_inst = {}
                for k, v in line.instantiation_map.items():
                    if isinstance(v, str):
                        if constant == v:
                            new_inst[k] = variable
                        else:
                            new_inst[k] = v
                    else:
                        if constant in v.constants() or constant in v.variables():
                            new_inst[k] = v.substitute({constant: Term(variable)})
                        else:
                            new_inst[k] = v

                new_proof_lines.append(Proof.AssumptionLine(new_formula, new_ass, new_inst))
            elif isinstance(line, Proof.TautologyLine):
                new_proof_lines.append(Proof.TautologyLine(line.formula.substitute({constant: Term(variable)})))

            elif isinstance(line, Proof.MPLine):
                new_proof_lines.append(Proof.MPLine(line.formula.substitute({constant: Term(variable)}),
                                                    line.antecedent_line_number, line.conditional_line_number))
            elif isinstance(line, Proof.UGLine):
                new_proof_lines.append(Proof.UGLine(line.formula.substitute({constant: Term(variable)}),
                                                    line.predicate_line_number))
        else:
            new_proof_lines.append(line)

    return Proof(new_proof_ass, new_proof_conc, new_proof_lines)


def _helper_for_ass(constant, variable, ass):
    if constant in ass.formula.constants():
        new_ass = ass.formula.substitute({constant: Term(variable)})
        new_temp = set()
        for temp in ass.templates:
            if temp == constant:
                new_temp.add(variable)
            else:
                new_temp.add(temp)

        return Schema(new_ass, new_temp)
    else:
        return ass


def eliminate_existential_witness_assumption(proof: Proof, constant: str,
                                             witness: Formula,
                                             existential: Formula) -> Proof:
    """Converts the given proof of a contradiction, whose assumptions/axioms
    include `existential` and `witness`, where the latter is an existential
    witness of the former, to a proof of a contradiction from the same
    assumptions without `witness`.

    Parameters:
        proof: valid proof of a contradiction from one or more
            assumptions/axioms that are all sentences and that include
            `~predicates.prover.Prover.AXIOMS`.
        existential: assumption of the given proof that is existentially
            quantified.
        witness: assumption of the given proof that is obtained from the
            predicate of `existential` by replacing all free occurrences of the
            existential quantification variable by some constant that does not
            appear in any assumption of the given proof except for this
            assumption.

    Returns:
        A valid proof of a contradiction from the assumptions/axioms of the
        proof except `witness`.
    """
    assert proof.is_valid()
    assert is_constant(constant)
    assert Schema(witness) in proof.assumptions
    assert Schema(existential) in proof.assumptions
    assert existential.root == 'E'
    assert witness == \
           existential.predicate.substitute(
               {existential.variable: Term(constant)})
    for assumption in proof.assumptions:
        assert len(assumption.formula.free_variables()) == 0
    for assumption in proof.assumptions.difference({Schema(witness)}):
        assert constant not in assumption.formula.constants()
    # Task 12.7.2

    new_var = 'zz'
    new_wit = witness.substitute({constant: Term(new_var)})
    replaced = replace_constant(proof, constant, new_var)
    contr_proof = proof_by_way_of_contradiction(replaced, new_wit)
    new_existential = Formula('E', new_var, existential.predicate.substitute({existential.variable: Term(new_var)}))
    prover = Prover(contr_proof.assumptions)
    line1 = prover.add_proof(contr_proof.conclusion, contr_proof)

    line2 = prover.add_free_instantiation(Formula("~", existential.predicate), line1,
                                          {new_var: Term(existential.variable)})
    line3 = prover.add_tautological_implication(Formula("->", existential.predicate, Formula("~", existential)),
                                                {line2})
    line35 = prover.add_tautological_implication(Formula("->", new_wit, Formula("~", new_existential)), {line1})
    line4 = prover.add_assumption(existential)
    line5 = prover.add_existential_derivation(Formula("~", existential), line4, line3)
    line6 = prover.add_tautological_implication(Formula('&', existential, Formula("~", existential)), {line4, line5})

    return prover.qed()


def existential_closure_step(sentences: AbstractSet[Formula]) -> Set[Formula]:
    """Augments the given sentences with an existential witness that uses a new
    constant name, for each existentially quantified sentences from these
    sentences for which an existential witness is missing.

    Parameters:
        sentences: prenex-normal-form sentences to augment with any missing
            existential witnesses.

    Returns:
        A set of all of the given sentences, and in addition for every
        existentially quantified sentence from the given sentences, a formula
        obtained from the predicate of that quantified sentence by replacing all
        occurrences of the quantification variable with a new constant name
        obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_constant_name_generator`\ ``)``.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    # Task 12.8

    new_sen = set()
    new_sen.update(sentences)
    old_vars = set()
    for sentence in sentences:
        old_vars.update(sentence.constants())
    for sentence in sentences:
        if sentence.root == 'E':
            predicate = sentence.predicate
            for var in old_vars:
                if predicate.substitute(({sentence.variable: Term(var)})) in new_sen:
                    break
            else:
                new_var = next(fresh_constant_name_generator)
                new_sen.add(predicate.substitute({sentence.variable: Term(new_var)}))

    return new_sen
