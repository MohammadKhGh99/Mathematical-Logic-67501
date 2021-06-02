# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: propositions/syntax.py

"""Syntactic handling of propositional formulas."""

from __future__ import annotations
from functools import lru_cache
from typing import Mapping, Optional, Set, Tuple, Union

from logic_utils import frozen, memoized_parameterless_method
import re

OPS = "&|\\||<->|\\+|->|-&|-\\|"


def _check_parenthesis(string):
    """
    this function checks the validity parenthesis order in the formula
    :param string: the formula to check
    :return: true if good, false otherwise
    """
    exp = re.compile(
        "^\\(((~?(?:[p-z]\\d*|[TF]|\\s*\\(.+\\)\\s*))(" + OPS + ")(~?(?:[p-z]\\d*|[TF]|\\s*\\(.+\\)\\s*)))\\)")
    if not exp.match(string):
        return False
    else:
        par = 0
        legal = False
        for s in string:
            if legal:
                return False
            if s == '(':
                par += 1
            elif s == ')':
                par -= 1
            if par == 0:
                legal = True
        return True


def _get_variables(formula, all_variables):
    if is_variable(formula.root):
        all_variables.append(formula.root)
    elif is_unary(formula.root):
        _get_variables(formula.first, all_variables)
    elif formula.root == '&' or formula.root == '|' or formula.root == "->":
        _get_variables(formula.first, all_variables)
        _get_variables(formula.second, all_variables)


def _check_sides(left, right, not_exp, form):
    """
    this function checks if the left and right sides of formula
    :param left: the left side
    :param right: the right side
    :param not_exp: not expression check
    :param form: form check
    :return: true if one from each side is true, false otherwise
    """
    left_var_const = is_constant(left) or is_variable(left)
    left_exp_check = not_exp.match(left) or not form.match(left)
    left_check = left_var_const or left_exp_check or _check_parenthesis(left)
    right_var_const = is_constant(right) or is_variable(right)
    right_exp_check = not_exp.match(right) or not form.match(right)
    right_check = right_var_const or right_exp_check or _check_parenthesis(right)
    return left_check and right_check


@lru_cache(maxsize=100)  # Cache the return value of is_variable
def is_variable(string: str) -> bool:
    """Checks if the given string is an atomic proposition.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is an atomic proposition, ``False``
        otherwise.
    """
    return string[0] >= 'p' and string[0] <= 'z' and (len(string) == 1 or string[1:].isdigit())


@lru_cache(maxsize=100)  # Cache the return value of is_constant
def is_constant(string: str) -> bool:
    """Checks if the given string is a constant.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a constant, ``False`` otherwise.
    """
    return string == 'T' or string == 'F'


@lru_cache(maxsize=100)  # Cache the return value of is_unary
def is_unary(string: str) -> bool:
    """Checks if the given string is a unary operator.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a unary operator, ``False`` otherwise.
    """
    return string == '~'


@lru_cache(maxsize=100)  # Cache the return value of is_binary
def is_binary(string: str) -> bool:
    """Checks if the given string is a binary operator.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a binary operator, ``False`` otherwise.
    """
    # return string == '&' or string == '|' or string == '->'
    # For Chapter 3:
    return string in {'&', '|', '->', '+', '<->', '-&', '-|'}


@frozen
class Formula:
    """An immutable propositional formula in tree representation, composed from
    atomic propositions, and operators applied to them.

    Attributes:
        root (`str`): the constant, atomic proposition, or operator at the root
            of the formula tree.
        first (`~typing.Optional`\\[`Formula`]): the first operand to the root,
            if the root is a unary or binary operator.
        second (`~typing.Optional`\\[`Formula`]): the second operand to the
            root, if the root is a binary operator.
    """
    root: str
    first: Optional[Formula]
    second: Optional[Formula]

    def __init__(self, root: str, first: Optional[Formula] = None,
                 second: Optional[Formula] = None):
        """Initializes a `Formula` from its root and root operands.

        Parameters:
            root: the root for the formula tree.
            first: the first operand to the root, if the root is a unary or
                binary operator.
            second: the second operand to the root, if the root is a binary
                operator.
        """
        if is_variable(root) or is_constant(root):
            assert first is None and second is None
            self.root = root
        elif is_unary(root):
            assert first is not None and second is None
            self.root, self.first = root, first
        else:
            assert is_binary(root)
            assert first is not None and second is not None
            self.root, self.first, self.second = root, first, second

    @memoized_parameterless_method
    def __repr__(self) -> str:
        """Computes the string representation of the current formula.

        Returns:
            The standard string representation of the current formula.
        """
        rep = ""
        if is_unary(self.root):
            rep += self.root
            if self.first is not None:
                rep += str(self.first)
        elif is_binary(self.root):
            rep += '('
            if self.first is not None:
                rep += str(self.first)
            if self.root != '~':
                rep += self.root
            if self.second is not None:
                rep += str(self.second)
            rep += ')'
        else:
            rep += self.root
        return rep
        # Task 1.1

    def __eq__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Formula` object that equals the
            current formula, ``False`` otherwise.
        """
        return isinstance(other, Formula) and str(self) == str(other)

    def __ne__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Formula` object or does not
            equal the current formula, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    @memoized_parameterless_method
    def variables(self) -> Set[str]:
        """Finds all atomic propositions (variables) in the current formula.

        Returns:
            A set of all atomic propositions used in the current formula.
        """
        my_set = set()
        if is_unary(self.root):
            if self.first is not None:
                tmp = self.first.variables()
                if len(tmp) != 0:
                    my_set.update(tmp)
        elif is_binary(self.root):
            if self.first is not None:
                tmp = self.first.variables()
                if len(tmp) != 0:
                    my_set.update(tmp)
            if self.second is not None:
                tmp = self.second.variables()
                if len(tmp) != 0:
                    my_set.update(tmp)
        else:
            if not is_constant(self.root):
                my_set.add(self.root)
        return my_set
        # Task 1.2

    @memoized_parameterless_method
    def operators(self) -> Set[str]:
        """Finds all operators in the current formula.

        Returns:
            A set of all operators (including ``'T'`` and ``'F'``) used in the
            current formula.
        """
        my_set = set()
        if is_constant(self.root):
            my_set.add(self.root)
        elif is_binary(self.root) or is_unary(self.root):
            my_set.add(self.root)
            if self.first is not None:
                tmp = self.first.operators()
                if len(tmp) != 0:
                    my_set.update(tmp)
            if self.root != '~' and self.second is not None:
                tmp = self.second.operators()
                if len(tmp) != 0:
                    my_set.update(tmp)
        return my_set
        # Task 1.3

    @staticmethod
    def _helper(string):
        par = 0
        first = ""
        second = ""
        root = ""
        text = ""
        i = 0
        while i < len(string):
            text += string[i]
            if string[i] == '(':
                par += 1
            elif string[i] == ')' and par != 0:
                par -= 1
            if par == 0 and (i + 1 == len(string) or first == ""):
                if len(string) > i + 1:
                    first = text
                    root_search = re.compile("(" + OPS + ")")
                    match = root_search.match(string[i + 1:i + 4])
                    root = match.group(1)
                    i += len(root) + 1
                    text = ""
                    continue
                elif len(string) == i + 1:
                    if first != "":
                        second = text
                    else:
                        first = text
                text = ""
            i += 1
        return root, first, second

    @staticmethod
    def _parse_prefix(string: str) -> Tuple[Union[Formula, None], str]:
        """Parses a prefix of the given string into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A pair of the parsed formula and the unparsed suffix of the string.
            If the given string has as a prefix a variable name (e.g.,
            ``'x12'``) or a unary operator follows by a variable name, then the
            parsed prefix will include that entire variable name (and not just a
            part of it, such as ``'x1'``). If no prefix of the given string is a
            valid standard string representation of a formula then returned pair
            should be of ``None`` and an error message, where the error message
            is a string with some human-readable content.
        """
        string = string.strip()
        root = ""
        msg = ""
        first, second, result = None, None, None
        if len(string) == 0:
            result = None
        else:
            form_str = "(~*(?:[p-z]\\d*|[TF]|\\s*\\(.+\\)\\s*))(" + OPS + ")(~*(?:[p-z]\\d*|[TF]|\\s*\\(.+\\)\\s*))"
            exp = re.compile("^\\((" + form_str + ")\\)$")
            form = re.compile(form_str)
            match = exp.match(string)
            not_exp = re.compile("^~(.+)")
            not_match = not_exp.match(string)
            const_exp = re.compile("([TF])(.*)")
            const_match = const_exp.match(string)
            var_exp = re.compile("([p-z]\\d*)(.*)")
            var_match = var_exp.match(string)
            flag = False
            if var_match:
                flag = True
                root = var_match.group(1)
                msg = var_match.group(2)
            elif not_match:
                flag = True
                temp = Formula._parse_prefix(not_match.group(1))
                if temp[0] is not None:
                    root = '~'
                    first = temp[0]
                    msg = temp[1]
            elif match:
                par = 0
                legal = ""
                found = False
                for s in match.group(0):
                    if s == '(' and found is False:
                        par += 1
                    elif s == ')' and found is False:
                        par -= 1
                    if found is False:
                        legal += s
                    else:
                        msg += s
                    found = True if par == 0 else False
                match = exp.match(legal)
                if legal[0] == legal[1] == '(' and legal[-1] == legal[-2] == ')':
                    root, first_temp, second_temp = Formula._helper(legal[1:-1])
                    first = Formula._parse_prefix(first_temp)[0]
                    second = Formula._parse_prefix(second_temp)[0] if second_temp != "" else None
                    flag = True
                else:
                    inner_match = form.match(match.group(1))
                    inner_match = match
                    # inner_match = re.search(".*",match.group(1))
                    # if legal[]
                    # inner_match = form.match(legal)
                    flag1 = False
                    if inner_match:
                        left = inner_match.group(2)
                        right = inner_match.group(4)
                        if _check_sides(left, right, not_exp, form):
                            left_temp = Formula._parse_prefix(left)
                            flag1 = True
                            right_temp = Formula._parse_prefix(right)
                            first = left_temp[0]
                            second = right_temp[0]
                            root = inner_match.group(3)
                    flag = True if flag1 else False
            elif const_match:
                flag = True
                root = const_match.group(1)
                msg = const_match.group(2)
            if flag:
                result = Formula(root, first, second)
        return result, msg
        # Task 1.4

    @staticmethod
    def is_formula(string: str) -> bool:
        """Checks if the given string is a valid representation of a formula.

        Parameters:
            string: string to check.

        Returns:
            ``True`` if the given string is a valid standard string
            representation of a formula, ``False`` otherwise.
        """
        parsed = Formula._parse_prefix(string)
        return parsed[0] is not None and parsed[1] == ""
        # Task 1.5

    @staticmethod
    def parse(string: str) -> Formula:
        """Parses the given valid string representation into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A formula whose standard string representation is the given string.
        """
        assert Formula.is_formula(string)
        return Formula._parse_prefix(string)[0]
        # Task 1.6

    # Optional tasks for Chapter 1

    def polish(self) -> str:
        """Computes the polish notation representation of the current formula.

        Returns:
            The polish notation representation of the current formula.
        """
        # Optional Task 1.7

    @staticmethod
    def parse_polish(string: str) -> Formula:
        """Parses the given polish notation representation into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A formula whose polish notation representation is the given string.
        """
        # Optional Task 1.8

    def substitute_variables(self, substitution_map: Mapping[str, Formula]) -> Formula:
        """Substitutes in the current formula, each variable `v` that is a key
        in `substitution_map` with the formula `substitution_map[v]`.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.

        Returns:
            The formula resulting from performing all substitutions. Only
            variables originating in the current formula are substituted (i.e.,
            variables originating in one of the specified substitutions are not
            subjected to additional substitutions).

        Examples:
            # >>> Formula.parse('((p->p)|r)').substitute_variables(
            # ...     {'p': Formula.parse('(q&r)'), 'r': Formula.parse('p')})
            (((q&r)->(q&r))|p)
        """
        for variable in substitution_map:
            assert is_variable(variable)
        # Task 3.3

        if self.root in substitution_map.keys():
            return substitution_map[self.root]
        elif is_binary(self.root):
            first = self.first.substitute_variables(substitution_map)
            second = self.second.substitute_variables(substitution_map)
            return Formula(self.root, first, second)
        elif is_unary(self.root):
            first = self.first.substitute_variables(substitution_map)
            return Formula(self.root, first)
        else:
            return self

    def substitute_operators(self, substitution_map: Mapping[str, Formula]) -> Formula:
        """Substitutes in the current formula, each constant or operator `op`
        that is a key in `substitution_map` with the formula
        `substitution_map[op]` applied to its (zero or one or two) operands,
        where the first operand is used for every occurrence of ``'p'`` in the
        formula and the second for every occurrence of ``'q'``.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.

        Returns:
            The formula resulting from performing all substitutions. Only
            operators originating in the current formula are substituted (i.e.,
            operators originating in one of the specified substitutions are not
            subjected to additional substitutions).

        Examples:
            # >>> Formula.parse('((x&y)&~z)').substitute_operators(
            # ...     {'&': Formula.parse('~(~p|~q)')})
            ~(~~(~x|~y)|~~z)
        """
        for operator in substitution_map:
            assert is_binary(operator) or is_unary(operator) or is_constant(operator)
            assert substitution_map[operator].variables().issubset({'p', 'q'})
        # Task 3.4

        variables = dict()
        if self.root in substitution_map.keys():
            if is_unary(self.root):
                variables['p'] = self.first.substitute_operators(substitution_map)
            elif is_binary(self.root):
                variables['p'] = self.first.substitute_operators(substitution_map)
                variables['q'] = self.second.substitute_operators(substitution_map)
            elif is_constant(self.root):
                return substitution_map[self.root]
            return substitution_map[self.root].substitute_variables(variables)
        else:
            first, second = None, None
            if is_unary(self.root):
                if is_constant(str(self.first)) and str(self.first) in substitution_map.keys():
                    return Formula(self.root, substitution_map[str(self.first)])
                first = self.first.substitute_operators(substitution_map)
            elif is_binary(self.root):
                first = self.first.substitute_operators(substitution_map)
                second = self.second.substitute_operators(substitution_map)
            return Formula(self.root, first, second)
