# automata-safa

This is a tool for constructing fairly nice symbolic alternating finite automata with bitvector
symbols. It's under vast reconstruction.

# Format Specification

The basic input/output format used in this tool is a custom `.afa` format. It's focused on
simplicity of specification and parsing, while being practical and readable for human. Readable only
if the human is not a whitespace masochist.

## Whitespace Agnosticism

Format is whitespace agnostic: you can remove or add any whitespace anywhere without changing
the abstract syntax tree. Example:
```
@kInitialFormula: s0
@kFinalFormula: !s0
@s0: kFalse
```
has the same meaning as
```
@ kInitialFormula  : s0 @kFinalFormula: !s0 @ s0: kFalse
```
and also the same as
```
@kInitialFormula:s0@kFinalFormula:!s0@s0:kFalse
```

That simplifies our parser: we remove all whitespace in advance and we don't have to deal with it at
all anymore.

## Definitions

The file is composed of a list of definitions. The character reserved for starting each definition
is `@`. Then, there is the definition's header, terminated by the reserved character `:`. Finally,
the content follows.

The header, nor the content, cannot contain any of the reserved characters.

## Identifiers

The identifier consists of a type prefix followed immediately by a name. Currently, we have four
types:

- `k` is a keyword
- `s` is a state
- `a` is a symbolic variable
- `f` is a shareable subformula

A name is a string of case sensitive alphanumeric characters and underscores in any order. UTF8
could work too but it's not tested at all, please just use ASCII, the world will thank you. Thank
you.

## Formula

A formula consists of

- nullary function symbols:
    - state identifiers (successors)
    - symbolic variables
    - `kTrue` denoting logical 1
    - `kFalse` denoting logical 0
- unary prefix operator `!`, denoting logical negation
- binary infix operators
    - `|` denoting disjunction
    - `&` denoting conjunction
- parentheses `()` for specifying precedence in a standard manner

Precedence:

- The operator `!` has higher precedence than `&` and `|`
- The operators `&` and `|` have incomparable precedence, mixing them without parentheses is a
  syntax error. For example `a1 & (a2 | a3)` and `(a1 & a2) | a3` is ok but `a1 & a2 | a3` is not
- As disjunction and conjunction are associative, we can omit parentheses in a subformula with
  homogeneous operators.  For example `a1 & (a2 & a3)` and `a1 & a2 & a3` are both ok.

## Header and Content

Currently, header is an identifier and content is a formula. But let's break it down. The header can
be

- a state identifier. The content is then a formula that is positive above states and defines the
  transition of the state.
- the `kInitialFormula` keyword. The content is again a formula that is positive above states. Its
  valuations (reduced to states) determine initial configurations of the automaton. Yes, they may
  contain also symbols and it makes sometimes sense. Use e.g. `addInit` if you hate this option.
- the `kFinalFormula` keyword. The content is a formula that is negative above states. Its
  valuations (reduced to states) determine final configurations of the automaton. Untested,
  not thinked about its use or problems, but symbols may be allowed and nonproblematic here as well.
  Use e.g. `removeFinals` or `removeFinalsHind` if you hate this option.
- a shareable subformula identifier. The content is then any formula and defines just a subformula
  that can be used in other definitions (but then, it has to satisfy the constraints of those
  definitions).

## Future work

Comments are not supported yet, we're planning to enclose comments in newly reserved characters `{}`
and special sequences in the comments will also be used to set additional attributes (e.g. `{Hello,
I'm a comment #state_color=red}` for a visualisation tool).
