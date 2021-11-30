---
title: FoS Coq notebook
jupyter:
  nbformat: 4
  nbformat_minor: 2
  kernelspec:
      display_name: "Coq"
      language: "coq"
      name: "coq"
  language_info:
      file_extension: ".v"
      mimetype: "text/x-coq"
      name: "coq"
      version: "8.9.1"
---

Adapted from a workshop given at [POPL 2008](https://www.cis.upenn.edu/~plclub/popl08-tutorial/).

# Before we begin

The point of this workshop is to give you a feel for what is it like to do
proofs in Coq, and also to illustrate what the Curry-Howard isomorphism really
is and what are its applications. This workshop is not graded, and you will not
see Coq during the exam (though there's a big chance you'll see Curry-Howard,
and you may see a fragment of CoC).

However, we cannot actually properly teach you how to do proofs in Coq or to
explain everything we will do in details, because we simply don't have enough
time for that. In case you are interested in knowing more, you can go through
this notebook (or its full version, check the README
[here](https://c4science.ch/diffusion/9452/)) in detail yourself, you could read
the [Software Foundations](https://softwarefoundations.cis.upenn.edu/) book, and
you could take a look at the
[Certified Programming with Dependent Types](http://adam.chlipala.net/cpdt/) book.

# Coq vs CoC

During the lecture, you have already seen how we can formulate CoC on paper.
In this notebook, we will be working with Coq, an interactive theorem assistant
with a type system based on an extension of CoC. The differences are slight,
but they are there, so let's start by inspecting them.

First things first: you can use the `Check` command to inspect types of terms.

```code
Check 0.
```

Naturally, we type `0` as `nat`.

```code
Check nat.
```

If we think in terms of set theory, then all `nat`s form a `Set`.
More to the point, `Set` in Coq is a kind of types that represent _data_
(more on this in a second).

We can define our own types with the `Inductive` command:

```code
Inductive nat' : Set :=
| zero'
| succ' (n : nat')
.
```

The `Inductive` command introduces an _inductive_ data type, inductive in this
case meaning being defined inductively. The above definition is basically the
same as the following Scala definition:

```scala
sealed trait Nat
final case object Zero extends Nat
final case class Succ(n: Nat) extends Nat
```

We say that `zero'` and `succ'` are _constructors_ for the `nat'` type, since they
are the fundamental/primitive way of constructing values of type `nat'`.  They are
themselves values or functions:

```code
Check zero'.
Check succ'.
```

And they can also be used to destruct/pattern match on values of type `nat'`:

```code
Fixpoint add (n : nat') (m : nat') : nat' :=
  match n with
  | zero'   => m
  | succ' n => add n (succ' m)
  end.
```

Coq is an interactive theorem assistant, so we'd like to use it to do some
proofs. Recall that by the Curry-Howard isomorphism, types are propositions and
terms that inhabit them are proofs that those propositions are true.
Then, if we want to do proofs about whether a number is even or not,
we first thing need to define a type for this proposition. Specifically, if `n`
is even, we would like to be able to construct a value of type `is_even' n`
(note that `is_even'` will need to be a type operator). We can define
`is_even'` as follows:


```code
Inductive is_even' : nat' -> Prop :=
| zero_even' : is_even' zero'
| double_succ_even' (n : nat') (p : is_even' n) : is_even' (succ' (succ' n))
.
```

As expected, we needed to annotate `is_even'` with `nat' -> Prop` as its type,
meaning it's a type operator from `nat'`s to a propositions (more on `Prop` in a
second). We have two constructors for this proposition, and both of them now
have annotations for their result types.

The first one, `zero_even'`, is a proof that 0 is even, and accordingly its type
is `is_even' zero'`. The other one is more complicated. We can understand it as
follows: if we want to prove that `n+2` is even, we need to have `n` (naturally)
and we need a proof that `n` is even -- a value of type `is_even' n`.

We can also type function literals with dependent function types.
For instance, say that we want to take a value of type `is_even' n` 
and we want to apply `double_succ_even'` to this value twice --
in this case, we want to take a value `n` and use it in a type,
so we need a term-dependent function type. Here's a definition of this
function in Coq:

```code
Check fun n : nat' => 
      fun p : is_even' n =>
      double_succ_even' _ (double_succ_even' _ p).
```

(Ignore the underscores for now, they are for boring arguments.)
The type of this value has the form `forall n : nat', t`.
That's the Coq equivalent of `(n : nat') -> t` (or `Π(n : nat')t`) 
from CoC.
Believe it or not, the above value is a proof of a trivial statement --
namely, that if `n` is even, then so is `n + 4`.
You can read out loud this value's type as follows: "for all n, n being even
implies that n+4 is even".

Why the underscores? Because `double_succ_even'` actually needs _two_ arguments,
an `n : nat'` and a `p : is_even' n`. The value for the first one can be figured
out based on the type of the second one, so with an underscore we can tell Coq
exactly that -- to figure out for us what value should be passed there. Neat.


## Sets and Props

Now, let's come back to `Set`. You may have noticed that for `is_even'`, we've
used `Prop` instead. What are those things? Well, here's what Coq can tell us:

```code
Check Set.
Check Prop.
```

Both `Set` and `Prop` are universes of "proper" types, in the sense of the `*`
sort you've seen in CoC, whereas `Type` is the equivalent of the "box" sort. How
come we have two variants of `*`? The short answer is: `Set` is the universe of
_data_, while `Prop` is the universe of _propositions_. That's honestly as much
as you need to understand in order to work with Coq.

The longer answer is that there's multiple small differences between them, all
aligned with the above intuition. Values from `Set` can be "extracted" to create
OCaml programs, while values from `Prop` cannot (and will in fact be ignored
when extracting values from `Set`). `Set` is predicative (meaning universal
types can't quantify over other universal types, like in Hindley-Milner), while
`Prop` is impredicative (meaning universal types are as powerful as in System
F). On the basis of the proof irrelevance principle, we assume that any two values
of the same type from `Prop` are equal. We do not do the same for types in `Set`,
which allows us the nice property that `0` is different from `1` and, more generally,
allows distinguishing any two values via, for instance, pattern matching.
There's other differences as well, but again: you don't actually need to know
any of them 99% of the time.

## Alternative form of Inductive

Recall the types of `zero'` and `succ'`:

```code
Check zero'.
Check succ'.
```

We could also define `nat'` by annotating each constructor with its type, as follows:

```coq
Inductive nat' : Set :=
| zero' : nat'
| succ' : nat' -> nat'
.
```

This is more convenient for more complex definitions, so we will be using this
form from now on.

Now, let's start the actual workshop!

# The NB language, back again

During your first project, you worked with the NB language, a trivial system
that had natural numbers, booleans and some basic operations for them.
In this notebook, we will be working with a very similar language.
We will use Coq to encode terms from the NB language, as well as basic judgments
and some simple proofs.

## Definitions
### Grammar and terms 

The grammar of our language would be defined as follows:

```
t  ::= "true"                   terms
     | "false"
     | "if" t "then" t "else" t
     | 0
     | "succ" t
     | "pred" t
     | "iszero" t
```

We will represent these terms in Coq with `tm`, an inductive data type:

``` code
Inductive tm : Set :=
| tm_true : tm
| tm_false : tm
| tm_if : tm -> tm -> tm -> tm
| tm_zero : tm
| tm_succ : tm -> tm
| tm_pred : tm -> tm
| tm_iszero : tm -> tm.
```

This definition is mostly straightforward -- for every rule in the grammar,
there's a corresponding constructor.
Using the above definition, we can create values corresponding to the terms in our language:

```code
(* Represents the term "if (iszero 0) then false else true" *)
Check (tm_if (tm_iszero tm_zero) tm_false tm_true).
```

### Definition of value

Next, we want to define what it means to be a _value_ in our language. While in
the original NB language we did so through grammar rules, it's equally valid to
define judgments which tells us which terms are boolean and numeric values.
The judgments will have the form `⊢ bvalue t` and `⊢ nvalue t` (for reasons
which will become clear in a second). They are defined as follows:

```
   ⊢ bvalue true       (b_true)
   ⊢ bvalue false      (b_false)

     ⊢ nvalue 0        (n_zero)
  
     ⊢ nvalue t
  -----------------    (n_succ)
  ⊢ nvalue (succ t)
```

How do we represent these judgments in Coq? Both `bvalue` and `nvalue` will need
to be type operators, like `is_even'`. A judgment is clearly a proposition, so
they will both be `Prop`s. The actual definitions are as follows:

```code
Inductive bvalue : tm -> Prop := 
| b_true : bvalue tm_true 
| b_false : bvalue tm_false.

Inductive nvalue : tm -> Prop :=
| n_zero : nvalue tm_zero
| n_succ : forall t,
    nvalue t ->
    nvalue (tm_succ t).
```

We have one constructor per each axiom and inference rule -- observe that the
constructor types are actually quite similar to the rules they represent.
We had to assign `n_succ` a dependent function type, since the corresponding
inference rule is implicitly quantified with a `t`.

Let's emphasize again what we have. The _type_ `nvalue t` represents the
_proposition_ that `t` is a numeric value. For instance, `nvalue (tm_succ
tm_zero)` represents the proposition that the successor of zero (or simply one)
is a numeric value. To show that this proposition is true, we need to construct
a value of said type. We can do that as follows:

```code
(** Note: n_succ needs two arguments, a `t : tm` and an `nvalue t`. *)
Check (n_succ tm_zero n_zero). 
```

As the last thing in this section, we will (finally) define what it means to be
a value. In Coq, `T \/ S` is the data type corresponding to the proof that
either `T` or `S` is true. If we use it, the definition is simple enough:

```code
Definition value (t : tm) : Prop :=
  bvalue t \/ nvalue t.
```

### Operational semantics

Having defined `tm`s and `value`s, we can define call-by-value operational
semantics for our language.
Formally, reduction was a relation between terms.
In Coq, we will define an inductive data type `eval (t : tm) (t' : tm) : Prop`
corresponding to the proposition that `t` evaluates to `t'` in a single step.
The definition is as follows:

```code
Inductive eval : tm -> tm -> Prop :=
| e_iftrue : forall t2 t3,
    eval (tm_if tm_true t2 t3) t2
| e_iffalse : forall t2 t3,
    eval (tm_if tm_false t2 t3) t3
| e_if : forall t1 t1' t2 t3,
    eval t1 t1' ->
    eval (tm_if t1 t2 t3) (tm_if t1' t2 t3)
| e_succ : forall t t',
    eval t t' ->
    eval (tm_succ t) (tm_succ t')
| e_predzero :
    eval (tm_pred tm_zero) tm_zero
| e_predsucc : forall t,
    nvalue t ->
    eval (tm_pred (tm_succ t)) t
| e_pred : forall t t',
    eval t t' ->
    eval (tm_pred t) (tm_pred t')
| e_iszerozero :
    eval (tm_iszero tm_zero) tm_true
| e_iszerosucc : forall t,
    nvalue t ->
    eval (tm_iszero (tm_succ t)) tm_false
| e_iszero : forall t t',
    eval t t' ->
    eval (tm_iszero t) (tm_iszero t').
```

If you don't feel comfortable with Coq syntax yet, compare the above with the
definition of beta-reduction from our first assignment.

Next, we define the multi-step evaluation relation `eval_many`, corresponding to multi-step beta-reduction.

Its inference rules are:

```
 -------------  (m_refl)
 eval_many t t 
 
 eval t t'    eval_many t' u
 ---------------------------  (m_step)
       eval_many t u
```

And its definition is:

```code
Inductive eval_many : tm -> tm -> Prop :=
| m_refl : forall t,
    eval_many t t
| m_step : forall t t' u,
    eval t t' ->
    eval_many t' u ->
    eval_many t u.
```

<!--
### Aside

You may be surprised that we defined data types for propositions that a term is
a value and that a term evaluates to another term. We could also define a function
that checks if a term is a value and returns a boolean, and a function that takes
a term and returns the term its argument reduces to. How come we didn't do that?

Here we could discuss decidability vs. undecidability and the fact that it's
difficult to do induction on fixpoints.
-->

### Exercises

**Note** The exercises below may be hard. If you find yourself stuck when doing
them, copy the definitions from solutions here - they will be useful later on.

**Exercise** Multi-step evaluation is often defined as the "reflexive,
transitive closure" of single-step evaluation. Write an inductively defined
relation `eval_rtc` that corresponds to that verbal description.

In case you get stuck or need a hint, you can find solutions to all the
exercises near the bottom of the file.

```code
(** Write your solution here *)
```
 
**Exercise** Sometimes it is more convenient to use a big-step semantics for a
language. Add the remaining constructors to finish the inductive definition
`full_eval` for the big-step semantics that corresponds to the small-step
semantics defined by `eval`. Build the inference rules so that `full_eval t v`
logically implies both `eval_many t v` and `value v`. In order to do this, you
may need to add the premise `nvalue v` to the appropriate cases.

Hint: You should end up with a total of 8 cases.

```code
(**
Inductive full_eval : tm -> tm -> Prop :=
| f_value : forall v,
    value v ->
    full_eval v v
| f_iftrue : forall t1 t2 t3 v,
    full_eval t1 tm_true ->
    full_eval t2 v ->
    full_eval (tm_if t1 t2 t3) v
| f_succ : forall t v,
    nvalue v ->
    full_eval t v ->
    full_eval (tm_succ t) (tm_succ v).
*)
```

## Proofs

So far, we've only seen proofs represented in Coq as manually-constructed
values. For any non-trivial proof value, it's rather inconvenient to manually
construct it.

Proof values are most easily built interactively, using tactics to manipulate a
proof state. A proof state consists of a set of goals (propositions or types for
which you must produce an inhabitant), each with a context of hypotheses
(inhabitants of propositions or types you are allowed to use). A proof state
begins initially with one goal (the statement of the lemma you are trying to
prove) and no hypotheses. A goal can be solved, and thereby eliminated, when it
exactly matches one of hypotheses in the context. A proof is completed when all
goals are solved.

Tactics can be used for forward reasoning (which, roughly speaking, means
modifying the hypotheses of a context while leaving the goal unchanged) or
backward reasoning (replacing the current goal with one or more new goals in
simpler contexts). Given the level of detail required in a formal proof, it
would be ridiculously impractical to complete a proof using forward reasoning
alone. However it is usually both possible and practical to complete a proof
using backward reasoning alone. Therefore, we focus almost exclusively on
backward reasoning in this tutorial. Of course, most people naturally use a
significant amount of forward reasoning in their thinking process, so it may
take you a while to become accustomed to getting by without it.

We use the keyword `Lemma` to state a new proposition we wish to prove.
(`Theorem` and `Fact` are exact synonyms for `Lemma`.) The keyword `Proof`,
immediately following the statement of the proposition, indicates the beginning
of a proof script. A proof script is a sequence of tactic expressions, each
concluding with a `.`. Once all of the goals are solved, we use the keyword
`Qed` to record the completed proof. If the proof is incomplete, we may tell Coq
to accept the lemma on faith by using `Admitted` instead of `Qed`.

We now proceed to introduce the specific proof tactics.

### Implication and universal quantification

```
    - [intros]
    - [apply]
    - [apply with (x := ...)]
```

Recall that both implication and universal quantification correspond to function
types and values. Accordingly, we can use the `intros` tactic to move
universally quantified variables and implication antecedents from the goal into
the context as hypotheses.

If our current goal corresponds to a conclusion of some implication `P`, we can
use the `apply P` tactic to prove our goal by proving the antecedents of `P`. If
you'd suspect from the name of the tactic that this corresponds to applying a
function, you'd be correct. Using `apply` allows building a proof value from the
bottom up.

#### Example 1

In the following example, we will create a value corresponding to a (still)
simple proposition. Step through every cell below to see how this value is
constructed.

```code
Lemma e_succ_pred_succ : forall t,
  nvalue t ->
  eval (tm_succ (tm_pred (tm_succ t))) (tm_succ t).
Proof.
```

```code
  (** Let [t] be a [tm]. *)
  intros t.
```

```code
  (** Assume that [t] is an [nvalue] (and let's call that
      assumption [Hn] for future reference). *)
  intros Hn.
```

```code
  (** By [e_succ], in order to prove our conclusion, it suffices
      to prove that [eval (tm_pred (tm_succ t)) t]. *)
  Check e_succ.
  apply e_succ.
```

```code
  (** That, in turn, can be shown by [e_predsucc], if we are
      able to show that [nvalue t]. *)
  Check e_predsucc.
  apply e_predsucc.
```

```code
  (** But, in fact, we assumed [nvalue t]. *)
  apply Hn.
```

``` code
Qed.
```

At this point, we have successfully concluded our proof; `e_succ_pred_succ` is a
value that can be used like any other value we have seen so far. It corresponds
to the following proof tree:

```
                        nvalue t
             ---------------------------- (e_predsucc)
             eval (tm_pred (tm_succ t)) t
    ------------------------------------------------ (e_succ)
    eval (tm_succ (tm_pred (tm_succ t))) (tm_succ t)
```

We can see the value we have constructed with the following command:

```code
Print e_succ_pred_succ.
```

Compare the value to the proof script above. Observe how function application in
the value corresponds to usages of `apply` tactic.

#### Example 2

Now consider, for a moment, the rule `m_step`:

```
    eval t t'  eval_many t' u
    ------------------------- (m_step)
          eval_many t u
```

If we have a goal such as `eval_many e1 e2`, we should be able to use `apply
m_step` in order to replace it with the goals `eval e1 t'` and `eval_many t'
e2`. But what exactly is `t'` here? When and how is it chosen? It stands to
reason the conclusion is justified if we can come up with any `t'` for which the
premises can be justified.

Now we note that, in the Coq syntax for the type of `m_step`, all three
variables `t`, `t'`, and `u` are universally quantified. The tactic `apply
m_step` will use pattern matching between our goal and the conclusion of
`m_step` to find the only possible instantiation of `t` and `u`. However, `apply
m_step` will raise an error since it does not know how it should instantiate
`t'`. In this case, the `apply` tactic takes a `with` clause that allows us to
provide this instantiation. This is demonstrated in the proof below. 

Observe how this works in the proof script below. The proof tree here gives a
visual representation of the proof term we are going to construct and the proof
script has again been annotated with the steps in English.

```
    Letting   s = tm_succ
              p = tm_pred
            lem = e_succ_pred_succ,

            nvalue t
    - - - - - - - - - - - - (lem)    --------------------- (m_refl)
    eval (s (p (s t))) (s t)         eval_many (s t) (s t)
    ------------------------------------------------------ (m_step)
                  eval_many (s (p (s t))) (s t)
```

``` code
Lemma m_succ_pred_succ : forall t,
  nvalue t ->
  eval_many (tm_succ (tm_pred (tm_succ t))) (tm_succ t).
Proof.
```

```code
  (** Let [t] be a [tm], and assume [nvalue t]. *)
  intros t Hn.
```

```code
  (** By [m_step], to show our conclusion, it suffices to find
      some [t'] for which
        [eval (tm_succ (tm_pred (tm_succ t))) t']
      and
        [eval t' (tm_succ t)].
      Let us choose [t'] to be [tm_succ t]. *)
  Check m_step.
  apply m_step with (t' := tm_succ t).
```

```code
    (** By the lemma [e_succ_pred_succ], to show
          [eval (tm_succ (tm_pred (tm_succ t))) (tm_succ t)],
        it suffices to show [nvalue t]. *)
    Check e_succ_pred_succ.
    apply e_succ_pred_succ.
```

```code
    (** And, in fact, we assumed [nvalue t]. *)
    apply Hn.
```

```code
    (** Moreover, by the rule [m_refl], we also may conclude
        [eval (tm_succ t) (tm_succ t)]. *)
    Check m_refl.
    apply m_refl.
```

```code
Qed.
```

#### Lab 1

Write proof scripts for the following lemmas, following the plain language descriptions.

These lemmas will be useful in later proofs.

``` code
Lemma m_one : forall t1 t2,
  eval t1 t2 ->
  eval_many t1 t2.
```

```code
  (** Let [t1] and [t2] be terms, and assume [eval t1 t2].  We
      may conclude [eval_many t1 t2] by [m_step] if we can find
      a term [t'] such that [eval t1 t'] and [eval_many t' t2].
      We will choose [t'] to be [t2].  Now we can show
      [eval t1 t2] by our assumption, and we can show
      [eval_many t2 t2] by [m_refl]. *)
Proof.
```

```code
  (* to finish *)
Admitted.
```

``` code
Lemma m_two : forall t1 t2 t3,
  eval t1 t2 ->
  eval t2 t3 ->
  eval_many t1 t3.
```

```code
  (** Let [t1], [t2], and [t3] be terms.  Assume [eval t1 t2]
      and [eval t2 t3].  By [m_step], we may conclude that
      [eval_many t1 t3] if we can find a term [t'] such that
      [eval t1 t'] and [eval_many t' t3].  Let's choose [t'] to
      be [t2].  We know [eval t1 t2] holds by assumption.  In
      the other case, by the lemma [m_one], to show [eval_many
      t2 t3], it suffices to show [eval t2 t3], which is one of
      our assumptions.  *)
Proof.
```

```code
  (* to finish *)
Admitted.
```

```code
Lemma m_iftrue_step : forall t t1 t2 u,
  eval t tm_true ->
  eval_many t1 u ->
  eval_many (tm_if t t1 t2) u.
```

```code
  (** Let [t], [t1], [t2], and [u] be terms.  Assume that
      [eval t tm_true] and [eval_many t1 u].  To show
      [eval_many (tm_if t t1 t2) u], by [m_step], it suffices to
      find a [t'] for which [eval (tm_if t t1 t2) t'] and
      [eval_many t' u].  Let us choose [t'] to be
      [tm_if tm_true t1 t2].  Now we can use [e_if] to show that
      [eval (tm_if t t1 t2) (tm_if tm_true t1 t2)] if we can
      show [eval t tm_true], which is actually one of our
      assumptions.  Moreover, using [m_step] once more, we can
      show [eval_many (tm_if tm_true t1 t2) u] where [t'] is
      chosen to be [t1].  Doing so leaves us to show
      [eval (tm_if tm_true t1 t2) t1] and [eval_many t1 u].  The
      former holds by [e_iftrue] and the latter holds by
      assumption. *)
Proof.
```

```code
  (* to finish *)
Admitted.
```

### Working with Conjunction and Disjunction

```
    - [split]
    - [left]
    - [right]
    - [destruct] (for conjunction and disjunction)
```

**Example** If `H` is the name of a conjunctive hypothesis, then `destruct H as p` will
replace the hypothesis `H` with its components using the names in the pattern
`p`. Observe the pattern in the example below.

```code
Lemma m_two_conj : forall t t' t'',
  eval t t' /\ eval t' t'' ->
  eval_many t t''.
Proof.
  intros t t' t'' H.
   destruct H as [ He1 He2 ].
   apply m_two with (t2 := t').
    apply He1.
    apply He2.
Qed.
```

**Example** Patterns may be nested to break apart nested structures. Note that
infix conjunction is right-associative, which is significant when trying to
write nested patterns. We will later see how to use `destruct` on many different
sorts of hypotheses.
 
```code
Lemma m_three_conj : forall t t' t'' t''',
  eval t t' /\ eval t' t'' /\ eval t'' t''' ->
  eval_many t t'''.
Proof.
  intros t t' t'' t''' H.
   destruct H as [ He1 [ He2 He3 ] ].
   apply m_step with (t' := t').
    apply He1.
    apply m_two with (t2 := t'').
      apply He2.
      apply He3.
Qed.
```

**Example** If your goal is a conjunction, use `split` to break it apart into
two separate subgoals.
 
```code
Lemma m_three : forall t t' t'' t''',
  eval t t' ->
  eval t' t'' ->
  eval t'' t''' ->
  eval_many t t'''.
Proof.
  intros t t' t'' t''' He1 He2 He3.
   apply m_three_conj with (t' := t') (t'' := t'').
    split.
      apply He1.
      split.
        apply He2.
        apply He3.
Qed.
```

**Exercise** Hint: You might find lemma `m_three` useful here.
 
```code
Lemma m_if_iszero_conj : forall v t2 t2' t3 t3',
  nvalue v /\ eval t2 t2' /\ eval t3 t3' ->
  eval_many (tm_if (tm_iszero tm_zero) t2 t3) t2' /\
  eval_many (tm_if (tm_iszero (tm_succ v)) t2 t3) t3'.
Proof.
```

```code
  (* to finish *)
Admitted.
```

**Example** If we have a disjunction in the context, we can use `destruct` to
reason by cases on the hypothesis. Note the syntax of the associated pattern.
 
```code
Lemma e_if_true_or_false : forall t1 t2,
  eval t1 tm_true \/ eval t1 tm_false ->
  eval_many (tm_if t1 t2 t2) t2.
Proof.
  intros t1 t2 H. destruct H as [ He1 | He2 ].
    apply m_two with (t2 := tm_if tm_true t2 t2).
      apply e_if. apply He1.
      apply e_iftrue.
    apply m_two with (t2 := tm_if tm_false t2 t2).
      apply e_if. apply He2.
      apply e_iffalse.
Qed.
```

## Reasoning by Cases and Induction

```
    - [destruct] (for inductively defined propositions)
    - [induction]
```

**Example** Use `destruct` to reason by cases on an inductively defined datatype
or proposition.

```code
Lemma e_iszero_nvalue : forall v,
  nvalue v ->
  eval (tm_iszero v) tm_true \/
  eval (tm_iszero v) tm_false.
Proof.
  intros v Hn.
```

```code
  destruct Hn.
```

```code
  (* Case [n_zero].
     Note how [v] becomes [tm_zero] in the goal. *)
    left.
```

```code
    apply e_iszerozero.
```

```code
  (* Case [n_succ].
     Note how [v] becomes [tm_succ v] in the goal. *)
    right.
```

```code
    apply e_iszerosucc. apply Hn.
Qed.
```

**Example** You can use `induction` to reason by induction on an inductively
defined datatype or proposition. This is the same as `destruct`, except that it
also introduces an induction hypothesis in the inductive cases.
 
```code
Lemma m_iszero : forall t u,
  eval_many t u ->
  eval_many (tm_iszero t) (tm_iszero u).
Proof.
  intros t u Hm. induction Hm.
    apply m_refl.
    apply m_step with (t' := tm_iszero t').
      apply e_iszero. apply H.
      apply IHHm.
Qed.
```

#### Lab 3
Work on the following exercise.

**Exercise** 

```code
Lemma m_trans : forall t t' u,
  eval_many t t' ->
  eval_many t' u ->
  eval_many t u.
```

```code
  (** We proceed by induction on the derivation of
      [eval_many t t'].
      Case [m_refl]: Since [t] and [t'] must be the same, our
        conclusion holds by assumption.
      Case [m_step]: Now let's rename the [t'] from the lemma
        statement to [u0] (as Coq likely will) and observe that
        there must be some [t'] (from above the line of the
        [m_step] rule) such that [eval t t'] and
        [eval_many t' u0].  Our conclusion follows from from
        an application of [m_step] with our new [t'] and our
        induction hypothesis, which allows us to piece together
        [eval_many t' u0] and [eval_many u0 u] to get
        [eval_many t' u]. *)
Proof.
```

```code
  (* to finish *)
Admitted.
```

**Exercise** Prove the following lemma.

Hint: You may be interested in some previously proved lemmas, such as `m_one`
and `m_trans`.

Note: Even though this lemma is in a comment, its solution is also at the
bottom. (Coq will give an error if we leave it uncommented since it mentions the
`eval_rtc` relation, which was the solution to another exercise.)

```code
(**
Lemma eval_rtc_many : forall t u,
  eval_rtc t u ->
  eval_many t u.
*)
```

**Exercise** Prove the following lemma.

```code
(**
Lemma eval_many_rtc : forall t u,
  eval_many t u ->
  eval_rtc t u.
*)
```


**Exercise** Prove the following lemma.

```code
(**
Lemma full_eval_to_value : forall t v,
  full_eval t v ->
  value v.
*)
```

# Solutions to Exercises

```code
Inductive eval_rtc : tm -> tm -> Prop :=
| r_eval : forall t t',
    eval t t' ->
    eval_rtc t t'
| r_refl : forall t,
    eval_rtc t t
| r_trans : forall t u v,
    eval_rtc t u ->
    eval_rtc u v ->
    eval_rtc t v.

Inductive full_eval : tm -> tm -> Prop :=
| f_value : forall v,
    value v ->
    full_eval v v
| f_iftrue : forall t1 t2 t3 v,
    full_eval t1 tm_true ->
    full_eval t2 v ->
    full_eval (tm_if t1 t2 t3) v
| f_iffalse : forall t1 t2 t3 v,
    full_eval t1 tm_false ->
    full_eval t3 v ->
    full_eval (tm_if t1 t2 t3) v
| f_succ : forall t v,
    nvalue v ->
    full_eval t v ->
    full_eval (tm_succ t) (tm_succ v)
| f_predzero : forall t,
    full_eval t tm_zero ->
    full_eval (tm_pred t) tm_zero
| f_predsucc : forall t v,
    nvalue v ->
    full_eval t (tm_succ v) ->
    full_eval (tm_pred t) v
| f_iszerozero : forall t,
    full_eval t tm_zero ->
    full_eval (tm_iszero t) tm_true
| f_iszerosucc : forall t v,
    nvalue v ->
    full_eval t (tm_succ v) ->
    full_eval (tm_iszero t) tm_false.

Lemma m_one_sol : forall t t',
  eval t t' ->
  eval_many t t'.
Proof.
  intros t t' He. apply m_step with (t' := t').
    apply He.
    apply m_refl.
Qed.

Lemma m_two_sol : forall t t' t'',
  eval t t' ->
  eval t' t'' ->
  eval_many t t''.
Proof.
  intros t t' t'' He1 He2. apply m_step with (t' := t').
    apply He1.
    apply m_one. apply He2.
Qed.

Lemma m_iftrue_step_sol : forall t t1 t2 u,
  eval t tm_true ->
  eval_many t1 u ->
  eval_many (tm_if t t1 t2) u.
Proof.
  intros t t1 t2 u He Hm.
   apply m_step with (t' := tm_if tm_true t1 t2).
    apply e_if. apply He.
    apply m_step with (t' := t1).
      apply e_iftrue.
      apply Hm.
Qed.

Lemma m_if_iszero_conj_sol : forall v t2 t2' t3 t3',
  nvalue v /\ eval t2 t2' /\ eval t3 t3' ->
  eval_many (tm_if (tm_iszero tm_zero) t2 t3) t2' /\
  eval_many (tm_if (tm_iszero (tm_succ v)) t2 t3) t3'.
Proof.
  intros v t2 t2' t3 t3' H.
   destruct H as [ Hn [ He1 He2 ] ]. split.
    apply m_three with
     (t' := tm_if tm_true t2 t3) (t'' := t2).
      apply e_if. apply e_iszerozero.
      apply e_iftrue.
      apply He1.
    apply m_three with
     (t' := tm_if tm_false t2 t3) (t'' := t3).
      apply e_if. apply e_iszerosucc. apply Hn.
      apply e_iffalse.
      apply He2.
Qed.

Lemma two_values_sol : forall t u,
  value t /\ value u ->
    bvalue t \/
    bvalue u \/
    (nvalue t /\ nvalue u).
Proof.
  unfold value. intros t u H.
   destruct H as [ [ Hb1 | Hn1 ] H2 ].
    left. apply Hb1.
    destruct H2 as [ Hb2 | Hn2 ].
      right. left. apply Hb2.
      right. right. split.
        apply Hn1.
        apply Hn2.
Qed.

Lemma m_trans_sol : forall t u v,
  eval_many t u ->
  eval_many u v ->
  eval_many t v.
Proof.
  intros t u v Hm1 Hm2. induction Hm1.
    apply Hm2.
    apply m_step with (t' := t').
      apply H.
      apply IHHm1. apply Hm2.
Qed.

Lemma eval_rtc_many_sol : forall t u,
  eval_rtc t u ->
  eval_many t u.
Proof.
  intros t u Hr. induction Hr.
    apply m_one. apply H.
    apply m_refl.
    apply m_trans with (t' := u).
      apply IHHr1.
      apply IHHr2.
Qed.

Lemma eval_many_rtc_sol : forall t u,
  eval_many t u ->
  eval_rtc t u.
Proof.
  intros t u Hm. induction Hm.
    apply r_refl.
    apply r_trans with (u := t').
      apply r_eval. apply H.
      apply IHHm.
Qed.

Lemma full_eval_to_value_sol : forall t v,
  full_eval t v ->
  value v.
Proof.
  intros t v Hf. induction Hf.
    apply H.
    apply IHHf2.
    apply IHHf2.
    right. apply n_succ. apply H.
    right. apply n_zero.
    right. apply H.
    left. apply b_true.
    left. apply b_false.
Qed.
```
