# Temporalog

Temporalog fuses Datalog and CTL. The semantics of the language rely on the so
called extended Kripke structures which which is yet to be published... For now,

For the semantically inclined: the temporal language is multimodal meaning we
have a family of operators. The accessibility relation is part of the modal
frame itself. Syntactic restrictions are used to tame the whole language going
bonkers. See the [language overview](#language-overview) for examples of these.
Hybrid logic operators are used to reify the state as a term and also to
directly modify it with the value of a term.

## Installation

Temporalog is implemented in Haskell and uses Stack to handle dependencies.
Stack installation instructions are available
[here](https://docs.haskellstack.org/en/stable/README/).

Then clone this repositroy and within the repository, run `stack build`.

To use the `temporalog` binary prepend it with `stack exec`.

For example,

`stack exec -- temporalog`

## Usage

To run a program use the `run` command.

```
stack exec -- temporalog run -f FILE
```

You can also see intermediate stages of compilation with the `pp` command. For a
full list of intermediate stages, use it without any arguments.

```
stack exec -- temporalog pp

```

For example if you want to see the pure Datalog output you can use the following

```
stack exec -- temporalog pp --exalog -f FILE
```

## Language overview

### Basic declarations

Temporalog is a typed Datalog implementation with obligatory declarations. The
three basic types are `text`, `int`, and `bool`.

For example, we can declare an `ancestor` predicate of arity two with both
parameters having a `text` type as follows:

```
.pred ancestor(text,text).
```

Temporal predicates are declared via `@` after the declaration specifying which
binary predicate should be used as the accessibility relation. For example, a
temporal predicate `day` with single `text` parameter using `clock` binary
predicate as its time predicate is declared using

```
.pred day(text) @ clock.
```

### Basic Datalog

Terms are either constants, variables, or wildcards. The `text` constants are
double quoted, integer constants are just integers, and boolean constants are
`true` or `false`. Variables are alphanumeric combinations of characters plus
`'` that start with an uppercase letters. Wildcards are alphanumeric characters
plus `'` that starts with `_`.

For example, a predicate `p` that has parameters `text`, `int`, and `bool` is
`p("apple", -42, false)` or it can be `p(_wild,Var42',true)`.

We use `,` for conjunction within the body, `;` for disjunction, and `!` for
negation. Nesting of operators are allowed. The precedence from tightest binding
to the

Clauses are of the form `head :- body.`; queries are of the form `?- body`; and
facts are of the form `head.`.

Anything following `%` is a comment (except within a `text` constant).

The archetypical logic program computing ancestors can be realised as follows:

```
advisor("Andrew Rice", "Mistral Contrastin").
advisor("Dominic Orchard", "Mistral Contrastin").
advisor("Andy Hopper", "Andrew Rice").
advisor("David Wheeler", "Andy Hopper").
advisor("Alan Mycroft", "Dominic Orchard").

ancestor(X,Y) :- advisor(X,Y).
ancestor(X,Z) :- advisor(X,Y), ancestor(Y,Z).

?- ancestor(X, "Mistral Contrastin").
?- ancestor(_X, "Mistral Contrastin").
?- ancestor("Mistral Contrastin", "Mistral Contrastin").
?- ancestor("David Wheeler", "Andrew Rice").
```

### Temporal constructs

The temporal operators are those of CTL. The temporal operators are `EX`, `AX`,
`EF`, `AF`, `EG`, `AG`, `EU`, and `AU`. The meanings of the operators are
standard.

`E/AX p`: `p` holds in some/all next states
`E/AF p`: it is possible to reach a point `p` holds in some/all paths
`E/AG p`: `p` continuously holds in some/all paths
`E/A[p U q]`: `p` holds in some/all paths until `q` holds

Here, a path is a (possibly infinite) trace of states (times).

## Hybrid operators

Modal operators provide an abstraction for time, but occasionally it is useful
to be able to observe time as well as to set it. This is where _hybrid temporal
logic_ comes into play. Temporalog provides two operators to this end. The
**jump** operator, `@`, sets the time and the **bind** operator, `|`, observes
it.

For example, if you want to have a temporal `weekend` predicate you can specify
it as

```
.pred day(text,text).
day("Monday","Tuesday").
day("Tuesday","Wednesday").
...
day("Sunday","Monday").

.pred weekend() @ day.
weekend() @ "Saturday".
weekend() @ "Sunday".

.preed weekday() @ day.
weekday() :- ! weekend().
```

We can also use the jump operator in clause and queries bodies. For example, `?-
(EF weekend()) @ "Monday"` asks if the weekend is reachable from Monday. I sure
hope, it is. However, `?- EF (weekend() @ "Monday")` asks if we can reach a
state Monday is a weekend. We wish, but to no avail...

The bind operator is useful when you want to interface the current time which is
implicit. If you are interested in weekdays that has six letters or less in
their names for example, you can write the following query.

```
?- | Day (weekday(), length(Day,N), leq(N,6)).
```

(At this point of the project length and leq are hypotheticals. Sorry!)

### Multimodality

Multiple time predicates can be associated with the same predicate. They are
space separated within the declaration. For example,

```
.pred timestamp() @ version clock.
```

If we actually define `timestamp`, we stumble upon an ambiguity.

```
timestamp() @ "CAFEBABE" @ "10:42 AM".
```

It is not clear which time we are trying to set. We don't pay any attention to
the ordering of time predicates in the declaration, so we need to disambiguiate.
The syntax for explicitly mentioning the time predicate after a temporal or
hybrid operator is `<time_predicate>` after the the relevant operator.

```
timestamp() @ <version> "CAFEBABE" @ <clock> "10:42 AM".
```

However, we can do a bit better. As soon as we set the inner time to be
evaluated at "CAFEBABE" the only sensible time predicate for the outer one is
`clock` by process of evaluation, so we can write the following instead.

```
timestamp() @ <version> "CAFEBABE" @ "10:42 AM".
```

In general, we allow these annotations to be left implicit whenever possible.
When we can't, the compiler complains about it.

Nullary predicates with multiple time predicates (such as `timestamp`) are good
for relating otherwise independent notions of time. However, when multiple
notions of time are repeatedly used together in clauses or queries, use of
`timestamp` becomes repetitive. If then such a nullary predicate should always
connect two notions of time in all queries and clauses, we can declare it to
be a **join** which in effect makes the compiler to insert the predicate in
simultaneous uses of the time predicates. The following is an example join
declaration:

```
.join timestamp.
```

Then if we have `p` with time predicate `version` and `q` with time predicate
`clock`, instead of writing `?- timestamp(), p(), q().`, we can just write `?-
p(), q().`.

The temporal operators are multimodal as well. If `p` has time predicates `t`
and `r`, we can query `?- AG <t> p` and `?- AG <r> p`. This is similar to
partial differentiation. We treat one notion of time as constant and use the CTL
operator semantics on the other accessibility relation.
