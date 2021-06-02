# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: predicates/syntax.py

"""Syntactic handling of predicate-logic expressions."""

from __future__ import annotations

from functools import lru_cache
from typing import AbstractSet, Mapping, Optional, Sequence, Set, Tuple, Union

from logic_utils import fresh_variable_name_generator as fresh, frozen, \
    memoized_parameterless_method

from propositions.syntax import Formula as PropositionalFormula, \
    is_variable as is_propositional_variable


def check_parentheses(s: str):
    """ Return the index of closing parentheses """
    stack = 0
    index_to_cut = 1
    for i, c in enumerate(s):
        if c == '(':
            # push to stack
            stack += 1
        elif c == ')':
            # pop stack
            stack -= 1
            if stack == 0:
                # mission accomplished
                break
        index_to_cut += 1
    return index_to_cut


def check_parentheses_square(s: str):
    """ Return the index of closing parentheses """
    stack = 0
    index_to_cut = 1
    for i, c in enumerate(s):
        if c == '[':
            # push to stack
            stack += 1
        elif c == ']':
            # pop stack
            stack -= 1
            if stack == 0:
                # mission accomplished
                break
        index_to_cut += 1
    return index_to_cut


def _handle_inner_parentheses(string: str):
    if not string:
        return []
    arguments = []
    while string:
        ans = Term._parse_prefix(string)
        if ans is None or ans[0] is None:
            return []
        else:
            arguments.append(ans[0])

        if ans[1]:
            if ans[1][0] == ',':
                string = ans[1][1:]
            else:
                return []
        else:
            return arguments


class ForbiddenVariableError(Exception):
    """Raised by `Term.substitute` and `Formula.substitute` when a substituted
    term contains a variable name that is forbidden in that context.

    Attributes:
        variable_name (`str`): the variable name that was forbidden in the
            context in which a term containing it was to be substituted.
    """
    variable_name: str

    def __init__(self, variable_name: str):
        """Initializes a `ForbiddenVariableError` from the offending variable
        name.

        Parameters:
            variable_name: variable name that is forbidden in the context in
                which a term containing it is to be substituted.
        """
        assert is_variable(variable_name)
        self.variable_name = variable_name


@lru_cache(maxsize=100)  # Cache the return value of is_constant
def is_constant(string: str) -> bool:
    """Checks if the given string is a constant name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a constant name, ``False`` otherwise.
    """
    return (((string[0] >= '0' and string[0] <= '9') or \
             (string[0] >= 'a' and string[0] <= 'd')) and \
            string.isalnum()) or string == '_'


@lru_cache(maxsize=100)  # Cache the return value of is_variable
def is_variable(string: str) -> bool:
    """Checks if the given string is a variable name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a variable name, ``False`` otherwise.
    """
    return string[0] >= 'u' and string[0] <= 'z' and string.isalnum()


@lru_cache(maxsize=100)  # Cache the return value of is_function
def is_function(string: str) -> bool:
    """Checks if the given string is a function name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a function name, ``False`` otherwise.
    """
    return string[0] >= 'f' and string[0] <= 't' and string.isalnum()


@frozen
class Term:
    """An immutable predicate-logic term in tree representation, composed from
    variable names and constant names, and function names applied to them.

    Attributes:
        root (`str`): the constant name, variable name, or function name at the
            root of the term tree.
        arguments (`~typing.Optional`\\[`~typing.Tuple`\\[`Term`, ...]]): the
            arguments to the root, if the root is a function name.
    """
    root: str
    arguments: Optional[Tuple[Term, ...]]

    def __init__(self, root: str, arguments: Optional[Sequence[Term]] = None):
        """Initializes a `Term` from its root and root arguments.

        Parameters:
            root: the root for the formula tree.
            arguments: the arguments to the root, if the root is a function
                name.
        """
        if is_constant(root) or is_variable(root):
            assert arguments is None
            self.root = root
        else:
            assert is_function(root)
            assert arguments is not None
            self.root = root
            self.arguments = tuple(arguments)
            assert len(self.arguments) > 0

    @memoized_parameterless_method
    def __repr__(self) -> str:
        """Computes the string representation of the current term.

        Returns:
            The standard string representation of the current term.
        """
        # Task 7.1
        answer = self.root
        if not (is_constant(self.root) or is_variable(self.root)):
            answer += '('
            for arg in range(len(self.arguments)):
                answer += str(self.arguments[arg])
                # if not the last
                if arg != len(self.arguments) - 1:
                    answer += ','
            answer += ')'
        return answer

    def __eq__(self, other: object) -> bool:
        """Compares the current term with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Term` object that equals the
            current term, ``False`` otherwise.
        """
        return isinstance(other, Term) and str(self) == str(other)

    def __ne__(self, other: object) -> bool:
        """Compares the current term with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Term` object or does not
            equal the current term, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    @staticmethod
    def _parse_prefix(string: str) -> Tuple[Term, str]:
        """Parses a prefix of the given string into a term.

        Parameters:
            string: string to parse, which has a prefix that is a valid
                representation of a term.

        Returns:
            A pair of the parsed term and the unparsed suffix of the string. If
            the given string has as a prefix a constant name (e.g., ``'c12'``)
            or a variable name (e.g., ``'x12'``), then the parsed prefix will be
            that entire name (and not just a part of it, such as ``'x1'``).
        """
        # Task 7.3.1

        if not string:
            return None, ''
        # first letter
        s = string[0]

        # variable:
        if is_variable(s):
            var = s
            counter = 1
            while counter < len(string) and string[counter].isalnum():
                var += string[counter]
                counter += 1

            return Term(var), string[counter:]

        # constant:
        elif is_constant(s):
            const = s
            if const == "_":
                return Term(const), string[1:]

            counter = 1
            while counter < len(string) and string[counter].isalnum():
                const += string[counter]
                counter += 1

            return Term(const), string[counter:]

        # function and others:
        elif is_function(s):
            func_name = s
            counter = 1
            while counter < len(string) and string[counter].isalnum():
                func_name += string[counter]
                counter += 1

            func_par = string[counter:]
            after_par = ''
            if func_par[0] == '(':
                par_end_index = check_parentheses(func_par)
                after_par = func_par[par_end_index:]  # todo hope index is the one after par
            else:
                return None, string

            func_par = func_par[:par_end_index][1:-1]  # everything inside parentheses
            arguments = _handle_inner_parentheses(func_par)
            if not arguments:
                return None, string

            return Term(func_name, tuple(arguments)), after_par

    @staticmethod
    def parse(string: str) -> Term:
        """Parses the given valid string representation into a term.

        Parameters:
            string: string to parse.

        Returns:
            A term whose standard string representation is the given string.
        """
        # Task 7.3.2
        ans, rest = Term._parse_prefix(string)
        return ans if ans and rest == "" else None

    @memoized_parameterless_method
    def constants(self) -> Set[str]:
        """Finds all constant names in the current term.

        Returns:
            A set of all constant names used in the current term.
        """
        # Task 7.5.1
        if is_variable(self.root):
            return set()
        elif is_constant(self.root):
            return {self.root}
        elif is_function(self.root):
            all_const = set()
            for arg in self.arguments:
                all_const.update(arg.constants())
            return all_const

    @memoized_parameterless_method
    def variables(self) -> Set[str]:
        """Finds all variable names in the current term.

        Returns:
            A set of all variable names used in the current term.
        """
        # Task 7.5.2
        if is_variable(self.root):
            return {self.root}
        elif is_constant(self.root):
            return set()
        elif is_function(self.root):
            all_var = set()
            for arg in self.arguments:
                all_var.update(arg.variables())
            return all_var

    @memoized_parameterless_method
    def functions(self) -> Set[Tuple[str, int]]:
        """Finds all function names in the current term, along with their
        arities.

        Returns:
            A set of pairs of function name and arity (number of arguments) for
            all function names used in the current term.
        """
        # Task 7.5.3
        ans = set()
        if is_function(self.root):
            ans.update({(self.root, len(self.arguments))})
            for arg in self.arguments:
                if is_function(arg.root):
                    ans.update(arg.functions())
        return ans

    def substitute(self, substitution_map: Mapping[str, Term],
                   forbidden_variables: AbstractSet[str] = frozenset()) -> Term:
        """Substitutes in the current term, each constant name `name` or
        variable name `name` that is a key in `substitution_map` with the term
        `substitution_map`\ ``[``\ `name`\ ``]``.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.
            forbidden_variables: variables not allowed in substitution terms.

        Returns:
            The term resulting from performing all substitutions. Only
            constant names and variable names originating in the current term
            are substituted (i.e., those originating in one of the specified
            substitutions are not subjected to additional substitutions).

        Raises:
            ForbiddenVariableError: If a term that is used in the requested
                substitution contains a variable from `forbidden_variables`.

        Examples:
            >>> Term.parse('f(x,c)').substitute(
            ...     {'c': Term.parse('plus(d,x)'), 'x': Term.parse('c')}, {'y'})
            f(c,plus(d,x))

            >>> Term.parse('f(x,c)').substitute(
            ...     {'c': Term.parse('plus(d,y)')}, {'y'})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: y
        """
        for element_name in substitution_map:
            assert is_constant(element_name) or is_variable(element_name)
        for variable in forbidden_variables:
            assert is_variable(variable)
        # Task 9.1

        if is_constant(self.root) or is_variable(self.root):
            if self.root not in substitution_map:
                return self
            for variable in substitution_map[self.root].variables():
                if variable in forbidden_variables:
                    raise ForbiddenVariableError(variable)
            return substitution_map[self.root]
        if is_function(self.root):
            arguments = [argument.substitute(substitution_map, forbidden_variables) for argument in self.arguments]
            return Term(self.root, arguments)


@lru_cache(maxsize=100)  # Cache the return value of is_equality
def is_equality(string: str) -> bool:
    """Checks if the given string is the equality relation.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is the equality relation, ``False``
        otherwise.
    """
    return string == '='


@lru_cache(maxsize=100)  # Cache the return value of is_relation
def is_relation(string: str) -> bool:
    """Checks if the given string is a relation name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a relation name, ``False`` otherwise.
    """
    return string[0] >= 'F' and string[0] <= 'T' and string.isalnum()


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
    return string == '&' or string == '|' or string == '->'


@lru_cache(maxsize=100)  # Cache the return value of is_quantifier
def is_quantifier(string: str) -> bool:
    """Checks if the given string is a quantifier.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a quantifier, ``False`` otherwise.
    """
    return string == 'A' or string == 'E'


@frozen
class Formula:
    """An immutable predicate-logic formula in tree representation, composed
    from relation names applied to predicate-logic terms, and operators and
    quantifications applied to them.

    Attributes:
        root (`str`): the relation name, equality relation, operator, or
            quantifier at the root of the formula tree.
        arguments (`~typing.Optional`\\[`~typing.Tuple`\\[`Term`, ...]]): the
            arguments to the root, if the root is a relation name or the
            equality relation.
        first (`~typing.Optional`\\[`Formula`]): the first operand to the root,
            if the root is a unary or binary operator.
        second (`~typing.Optional`\\[`Formula`]): the second
            operand to the root, if the root is a binary operator.
        variable (`~typing.Optional`\\[`str`]): the variable name quantified by
            the root, if the root is a quantification.
        predicate (`~typing.Optional`\\[`Formula`]): the predicate quantified by
            the root, if the root is a quantification.
    """
    root: str
    arguments: Optional[Tuple[Term, ...]]
    first: Optional[Formula]
    second: Optional[Formula]
    variable: Optional[str]
    predicate: Optional[Formula]

    def __init__(self, root: str, arguments_or_first_or_variable: Union[Sequence[Term], Formula, str],
                 second_or_predicate: Optional[Formula] = None):
        """Initializes a `Formula` from its root and root arguments, root
        operands, or root quantified variable and predicate.

        Parameters:
            root: the root for the formula tree.
            arguments_or_first_or_variable: the arguments to the root, if the
                root is a relation name or the equality relation; the first
                operand to the root, if the root is a unary or binary operator;
                the variable name quantified by the root, if the root is a
                quantification.
            second_or_predicate: the second operand to the root, if the root is
                a binary operator; the predicate quantified by the root, if the
                root is a quantification.
        """
        if is_equality(root) or is_relation(root):
            # Populate self.root and self.arguments
            assert second_or_predicate is None
            assert isinstance(arguments_or_first_or_variable, Sequence) and \
                   not isinstance(arguments_or_first_or_variable, str)
            self.root, self.arguments = root, tuple(arguments_or_first_or_variable)
            if is_equality(root):
                assert len(self.arguments) == 2
        elif is_unary(root):
            # Populate self.first
            assert isinstance(arguments_or_first_or_variable, Formula) and \
                   second_or_predicate is None
            self.root, self.first = root, arguments_or_first_or_variable
        elif is_binary(root):
            # Populate self.first and self.second
            assert isinstance(arguments_or_first_or_variable, Formula) and \
                   second_or_predicate is not None
            self.root, self.first, self.second = \
                root, arguments_or_first_or_variable, second_or_predicate
        else:
            assert is_quantifier(root)
            # Populate self.variable and self.predicate
            assert isinstance(arguments_or_first_or_variable, str) and \
                   is_variable(arguments_or_first_or_variable) and \
                   second_or_predicate is not None
            self.root, self.variable, self.predicate = \
                root, arguments_or_first_or_variable, second_or_predicate

    @memoized_parameterless_method
    def __repr__(self) -> str:
        """Computes the string representation of the current formula.

        Returns:
            The standard string representation of the current formula.
        """
        # Task 7.2
        # equality
        if is_equality(self.root):  # Populate self.first and self.second
            return str(self.arguments[0]) + '=' + str(self.arguments[1])

        # arguments
        elif is_relation(self.root):  # Populate self.root and self.arguments
            answer = self.root
            if not (is_constant(self.root) or is_variable(self.root)):
                answer += '('
                for arg in range(len(self.arguments)):
                    answer += str(self.arguments[arg])
                    # if not the last
                    if arg != len(self.arguments) - 1:
                        answer += ','
                answer += ')'
            return answer

        # unary
        elif is_unary(self.root):  # Populate self.first
            return self.root + str(self.first)

        # binary
        elif is_binary(self.root):  # Populate self.first and self.second
            return '(' + str(self.first) + self.root + str(self.second) + ')'

        # variables and predicate
        else:  # Populate self.variable and self.predicate
            return self.root + self.variable + '[' + str(self.predicate) + ']'

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

    @staticmethod
    def _parse_prefix(string: str) -> Tuple[Formula, str]:
        """Parses a prefix of the given string into a formula.

        Parameters:
            string: string to parse, which has a prefix that is a valid
                representation of a formula.

        Returns:
            A pair of the parsed formula and the unparsed suffix of the string.
            If the given string has as a prefix a term followed by an equality
            followed by a constant name (e.g., ``'c12'``) or by a variable name
            (e.g., ``'x12'``), then the parsed prefix will include that entire
            name (and not just a part of it, such as ``'x1'``).
        """
        # Task 7.4.1

        if not string:
            return None, ''

        # unary
        if is_unary(string[0]):
            s = string[1:]
            ans, rest = Formula._parse_prefix(s)
            if ans is None:
                return None, string
            else:
                return Formula("~", ans), rest
        # binary:
        elif string[0] == "(":
            index = check_parentheses(string)
            binary = string[1:index - 1]  # todo parenthesses check (cut the parenthesse from it)
            rest = string[index:]  # todo parenthesses check (after parenthesse to the end)

            first, binary_rest = Formula._parse_prefix(binary)
            if first is None:
                return None, string

            if binary_rest and (binary_rest[0] == "|" or binary_rest[0] == "&" or binary_rest[0:2] == "->"):
                if binary_rest[0] == "|" or binary_rest[0] == "&":
                    binary_root = binary_rest[0]
                    second_binary = binary_rest[1:]
                else:
                    binary_root = "->"
                    second_binary = binary_rest[2:]

                second, second_rest = Formula._parse_prefix(second_binary)
                if not second_rest:
                    return Formula(binary_root, first, second), rest

            return None, string
        # relation
        elif is_relation(string[0]):
            func_name = string[0]
            counter = 1
            while counter < len(string) and string[counter].isalnum():
                func_name += string[counter]
                counter += 1

            func_par = string[counter:]
            if func_par[0] == '(':
                par_end_index = check_parentheses(func_par)
                after_par = func_par[par_end_index:]  # todo hope index is the one after par
            else:
                return None, string

            func_par = func_par[:par_end_index][1:-1]  # everything inside parentheses
            if not func_par:
                return Formula(func_name, tuple()), after_par

            arguments = _handle_inner_parentheses(func_par)
            if not arguments:
                return None, string

            return Formula(func_name, tuple(arguments)), after_par
        # quantification
        elif is_quantifier(string[0]):
            root = string[0]
            if 'u' <= string[1] <= 'z':
                var = string[1]
                counter = 2
                while counter < len(string) and string[counter].isalnum():
                    var += string[counter]
                    counter += 1
            else:
                return None, string

            if string[counter] == '[':

                string = string[counter:]
                index = check_parentheses_square(string)
                square_inner = string[1:index - 1]  # todo parenthesses check (cut the parenthesse from it)
                rest = string[index:]

                ans, inner_rest = Formula._parse_prefix(square_inner)
                if inner_rest:
                    return None, ""

                return Formula(root, var, ans), rest

            else:
                return None, ''

        # equality:
        elif "=" in string:
            arguments = []
            first, rest = Term._parse_prefix(string)
            arguments.append(first)
            if arguments[0] is not None:
                if rest and rest[0] == "=":
                    second, rest = Term._parse_prefix(rest[1:])
                    arguments.append(second)
                else:
                    return None, string

                if arguments[1] is None:
                    return None, string
                else:
                    return Formula("=", arguments), rest

        else:
            return None, ''

    @staticmethod
    def parse(string: str) -> Formula:
        """Parses the given valid string representation into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A formula whose standard string representation is the given string.
        """
        # Task 7.4.2
        ans, rest = Formula._parse_prefix(string)
        return ans if ans and rest == "" else None

    @memoized_parameterless_method
    def constants(self) -> Set[str]:
        """Finds all constant names in the current formula.

        Returns:
            A set of all constant names used in the current formula.
        """
        # Task 7.6.1
        if is_equality(self.root) or is_relation(self.root):
            ans = set()
            for arg in self.arguments:
                ans.update(arg.constants())
            return ans
        elif is_unary(self.root):
            return self.first.constants()
        elif is_binary(self.root):
            return self.first.constants().union(self.second.constants())
        elif is_quantifier(self.root):
            return self.predicate.constants()

    @memoized_parameterless_method
    def variables(self) -> Set[str]:
        """Finds all variable names in the current formula.

        Returns:
            A set of all variable names used in the current formula.
        """
        # Task 7.6.2
        if is_equality(self.root) or is_relation(self.root):
            ans = set()
            for arg in self.arguments:
                ans.update(arg.variables())
            return ans
        elif is_unary(self.root):
            return self.first.variables()
        elif is_binary(self.root):
            return self.first.variables().union(self.second.variables())
        elif is_quantifier(self.root):
            return {self.variable}.union(self.predicate.variables())

    @memoized_parameterless_method
    def free_variables(self) -> Set[str]:
        """Finds all variable names that are free in the current formula.

        Returns:
            A set of every variable name that is used in the current formula not
            only within a scope of a quantification on that variable name.
        """
        # Task 7.6.3
        if is_equality(self.root) or is_relation(self.root):
            ans = set()
            for arg in self.arguments:
                ans.update(arg.variables())
            return ans
        elif is_unary(self.root):
            return self.first.free_variables()
        elif is_binary(self.root):
            return self.first.free_variables().union(self.second.free_variables())
        elif is_quantifier(self.root):
            return self.predicate.free_variables() - {str(self.variable)}

    @memoized_parameterless_method
    def functions(self) -> Set[Tuple[str, int]]:
        """Finds all function names in the current formula, along with their
        arities.

        Returns:
            A set of pairs of function name and arity (number of arguments) for
            all function names used in the current formula.
        """
        # Task 7.6.4

        ans = set()
        if is_equality(self.root) or is_relation(self.root):
            for arg in self.arguments:
                ans.update(arg.functions())
        elif is_unary(self.root):
            ans.update(self.first.functions())
        elif is_binary(self.root):
            ans.update(self.first.functions().union(self.second.functions()))
        elif is_quantifier(self.root):
            ans.update(self.predicate.functions())
        return ans

    @memoized_parameterless_method
    def relations(self) -> Set[Tuple[str, int]]:
        """Finds all relation names in the current formula, along with their
        arities.

        Returns:
            A set of pairs of relation name and arity (number of arguments) for
            all relation names used in the current formula.
        """
        # Task 7.6.5
        ans = set()
        if is_relation(self.root):
            ans.update({(self.root, len(self.arguments))})
        elif is_unary(self.root):
            ans.update(self.first.relations())
        elif is_binary(self.root):
            ans.update(self.first.relations().union(self.second.relations()))
        elif is_quantifier(self.root):
            ans.update(self.predicate.relations())
        return ans

    def substitute(self, substitution_map: Mapping[str, Term],
                   forbidden_variables: AbstractSet[str] = frozenset()) -> \
            Formula:
        """Substitutes in the current formula, each constant name `name` or free
        occurrence of variable name `name` that is a key in `substitution_map`
        with the term `substitution_map`\ ``[``\ `name`\ ``]``.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.
            forbidden_variables: variables not allowed in substitution terms.

        Returns:
            The formula resulting from performing all substitutions. Only
            constant names and variable names originating in the current formula
            are substituted (i.e., those originating in one of the specified
            substitutions are not subjected to additional substitutions).

        Raises:
            ForbiddenVariableError: If a term that is used in the requested
                substitution contains a variable from `forbidden_variables`
                or a variable occurrence that becomes bound when that term is
                substituted into the current formula.

        Examples:
            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,x)'), 'x': Term.parse('c')}, {'z'})
            Ay[c=plus(d,x)]

            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,z)')}, {'z'})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: z

            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,y)')})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: y
        """
        for element_name in substitution_map:
            assert is_constant(element_name) or is_variable(element_name)
        for variable in forbidden_variables:
            assert is_variable(variable)
        # Task 9.2

        # if is_unary(self.root):
        #     return Formula(self.root, self.first.substitute(substitution_map, forbidden_variables))
        if is_binary(self.root):
            first = self.first.substitute(substitution_map, forbidden_variables)
            second = self.second.substitute(substitution_map, forbidden_variables)
            return Formula(self.root, first, second)
        elif is_quantifier(self.root):
            forbidden = {self.variable}.union(forbidden_variables)
            sub_map = dict()
            for key, value in substitution_map.items():
                if self.variable != key:
                    sub_map[key] = value
            return Formula(self.root, self.variable, self.predicate.substitute(sub_map, forbidden))
        elif is_relation(self.root) or is_equality(self.root):
            arguments = [argument.substitute(substitution_map, forbidden_variables) for argument in self.arguments]
            return Formula(self.root, arguments)
        else:
            return Formula(self.root, self.first.substitute(substitution_map, forbidden_variables))


    def _helper(self, sub_map: dict):
        if is_unary(self.root):
            formula, dic = self.first._helper(sub_map)
            return PropositionalFormula(self.root, formula), dic
        elif is_binary(self.root):
            first_formula, first_map = self.first._helper(sub_map)
            second_formula, second_map = self.second._helper(sub_map)
            new_map = dict(first_map)
            for k, v in second_map.items():
                if v not in new_map.values():
                    new_map[k] = v
            return PropositionalFormula(self.root, first_formula, second_formula), first_map
        else:
            if self in sub_map.values():
                dic_keys = list(sub_map.keys())
                dic_values = list(sub_map.values())
                return PropositionalFormula.parse(dic_keys[dic_values.index(self)]), sub_map
            cur = str(next(fresh))
            sub_map[cur] = self
            return PropositionalFormula.parse(cur), sub_map

    def propositional_skeleton(self) -> Tuple[PropositionalFormula, Mapping[str, Formula]]:
        """Computes a propositional skeleton of the current formula.

        Returns:
            A pair. The first element of the pair is a propositional formula
            obtained from the current formula by substituting every (outermost)
            subformula that has a relation or quantifier at its root with an
            atomic propositional formula, consistently such that multiple equal
            such (outermost) subformulas are substituted with the same atomic
            propositional formula. The atomic propositional formulas used for
            substitution are obtained, from left to right, by calling
            `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``.
            The second element of the pair is a mapping from each atomic
            propositional formula to the subformula for which it was
            substituted.

        Examples:
            >>> formula = Formula.parse('((Ax[x=7]&x=7)|(x=7->~Q(y)))')
            >>> formula.propositional_skeleton()
            (((z1&z2)|(z2->~z3)), {'z1': Ax[x=7], 'z2': x=7, 'z3': Q(y)})
            >>> formula.propositional_skeleton()
            (((z4&z5)|(z5->~z6)), {'z4': Ax[x=7], 'z5': x=7, 'z6': Q(y)})
        """
        # Task 9.8

        return self._helper(dict())

    @staticmethod
    def from_propositional_skeleton(skeleton: PropositionalFormula,
                                    substitution_map: Mapping[str, Formula]) -> \
            Formula:
        """Computes a predicate-logic formula from a propositional skeleton and
        a substitution map.

        Arguments:
            skeleton: propositional skeleton for the formula to compute,
                containing no constants or operators beyond ``'~'``, ``'->'``,
                ``'|'``, and ``'&'``.
            substitution_map: mapping from each atomic propositional subformula
                of the given skeleton to a predicate-logic formula.

        Returns:
            A predicate-logic formula obtained from the given propositional
            skeleton by substituting each atomic propositional subformula with
            the formula mapped to it by the given map.

        Examples:
            >>> Formula.from_propositional_skeleton(
            ...     PropositionalFormula.parse('((z1&z2)|(z2->~z3))'),
            ...     {'z1': Formula.parse('Ax[x=7]'), 'z2': Formula.parse('x=7'),
            ...      'z3': Formula.parse('Q(y)')})
            ((Ax[x=7]&x=7)|(x=7->~Q(y)))
        """
        for operator in skeleton.operators():
            assert is_unary(operator) or is_binary(operator)
        for variable in skeleton.variables():
            assert variable in substitution_map
        # Task 9.10

        if is_unary(skeleton.root):
            return Formula(skeleton.root, Formula.from_propositional_skeleton(skeleton.first, substitution_map))
        elif is_binary(skeleton.root):
            first = Formula.from_propositional_skeleton(skeleton.first, substitution_map)
            second = Formula.from_propositional_skeleton(skeleton.second, substitution_map)
            return Formula(skeleton.root, first, second)
        else:
            return substitution_map[str(skeleton)]

