---
title: My notebook
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

# The NB language, back again

In this notebook, we will be working with a language very similar to the NB
language from the first assignment.

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

To represent the terms of this language in Coq, we will define `tm`, an
`Inductive` data type:

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

Compare the two definitions. For every rule in the grammar, there is a
corresponding _constructor_. Each constructor is a value in Coq that allows us
to obtain values of type `tm`. In contrast to the previous notebook, here we
annotate every constructor with a type. `tm_true` is a constructor corresponding
to the terminal rule `"true"` - it takes no arguments and is therefore annotated
with the simple type `tm`. `tm_succ` is a constructor corresponding to the
`"succ" t` rule - since the rule has a single subterm, the constructor is a
function from `tm` to `tm`.

Using the above definition, we can create values corresponding to the terms in our language:

```code
(* Represents "if (iszero 0) false true" *)
Check (tm_if (tm_iszero tm_zero) tm_false tm_true).
```

### Definition of value

Next, we want to define what it means to be a _value_ in our language. While in
the original NB language we did so through grammar rules, it's equally valid to
define a judgment which tells us which terms are boolean and numeric values
(correspondingly, `bvalue` and `nvalue`):

```
  ---------------  (b_true)
  ⊢ bvalue (true)

  ---------------- (b_false)
  ⊢ bvalue (false)

  
  ---------- (n_zero)
  ⊢ nvalue 0
  
     ⊢ nvalue t
  ----------------- (n_succ)
  ⊢ nvalue (succ t)
```

Recall that from Curry-Howard correspondence we know that types correspond to
propositions and values correspond to proofs. Therefore, we can represent the
above judgements in Coq by defining types corresponding to the judgments. Those
types are `bvalue t` and `nvalue t`. Being able to create a well-typed value of
type `nvalue t` is the same as being able to construct a proof that a given term
is an `nvalue`; same notion applies to  `bvalue t`.

We define said types as follows:

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

Those definitions should look similar to the inference rules above, although
they may also look slightly confusing. Before trying to understand their every
part, it may help to see how they are meant to be used.

Again, the _type_ `nvalue t` represents the _proposition_ that `t` is a numeric
value. For instance, `nvalue (tm_succ tm_zero)` represents the proposition that
the successor of zero (or simply one) is a numeric value. To show that this
proposition is true, we need to construct a value of said type. We can do that
as follows:

```code
Check (n_succ tm_zero n_zero).
```

You should now go back to the definitions and try to understand how they
represent their corresponding inference rules.

One thing that may still be puzzling are the `Set` and `tm -> Prop` annotation.
If you are suspecting that the second one mentions `tm ->` because the
corresponding type is a _type-level function_ from `tm` to `Prop`, you'd be correct:

```code
Check nvalue.
Check nvalue tm_zero.
```

The difference between `Set` and `Prop` is much more subtle and fundamental. To
put it briefly, types annotated as `Set` are meant to be used as data types,
while those annotated as `Prop` are meant to be used as propositions. Fully
explaining this distinction is beyond the scope of this course, but the above
intuition should serve you well enough.

As the last thing in this section, we will (finally) define what it means to be
a value. If you recall that `T \/ S` is the data type corresponding to the
proof that either `T` or `S`, the definition is simple enough:

```code
Definition value (t : tm) : Prop :=
  bvalue t \/ nvalue t.
```
### Operational semantics

Having defined `tm`s and `value`s, we can define call-by-value operational
semantics for our language. We will define an inductive data type `eval (t : tm)
(t' : tm) : Prop` corresponding to the proposition that `t` evaluates to `t'` in
a single step. The definition is as follows:

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

### Exercises

**Note** The exercises below may be hard. If you find yourself stuck when doing
them, copy the definitions from solutions here - they will be useful later on.

**Exercise** Multi-step evaluation is often defined as the "reflexive,
transitive closure" of single-step evaluation. Write an inductively defined
relation `eval_rtc` that corresponds to that verbal description.

In case you get stuck or need a hint, you can find solutions to all the
exercises near the bottom of the file.
 
**Exercise** Sometimes it is more convenient to use a big-step semantics for a
language. Add the remaining constructors to finish the inductive definition
`full_eval` for the big-step semantics that corresponds to the small-step
semantics defined by `eval`. Build the inference rules so that `full_eval t v`
logically implies both `eval_many t v` and `value v`. In order to do this, you
may need to add the premise `nvalue v` to the appropriate cases.

Hint: You should end up with a total of 8 cases.

```
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

``` code
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
 
``` code
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
 
``` code
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
 
``` code
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
 
``` code
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

``` code
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

``` code
    apply e_iszerosucc. apply Hn.
Qed.
```

**Example** You can use `induction` to reason by induction on an inductively
defined datatype or proposition. This is the same as `destruct`, except that it
also introduces an induction hypothesis in the inductive cases.
 
``` code
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

``` code
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

```
Lemma eval_rtc_many : forall t u,
  eval_rtc t u ->
  eval_many t u.
```

**Exercise** Prove the following lemma.

```
Lemma eval_many_rtc : forall t u,
  eval_many t u ->
  eval_rtc t u.
```


**Exercise** Prove the following lemma.

```
Lemma full_eval_to_value : forall t v,
  full_eval t v ->
  value v.
```

# Solutions to Exercises

``` code
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
