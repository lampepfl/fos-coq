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
above judgements in Coq by defining a type corresponding to each judgement.
Then, begin able to create a value of type `nvalue` is the same as being able to
construct a proof that a given term is an `nvalue`.

The definitions are as follows:

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

The _type_ `nvalue t` represents the _proposition_ that `t` is a numeric value.
For instance, `nvalue (tm_succ tm_zero)` represents the proposition that the
successor of zero (or simply one) is a numeric value. To show that this
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

Next, we define the multi-step evaluation relation `eval_many`:

```code
Inductive eval_many : tm -> tm -> Prop :=
| m_refl : forall t,
    eval_many t t
| m_step : forall t t' u,
    eval t t' ->
    eval_many t' u ->
    eval_many t u.
```

We say that a term is a `normal_form` if there is no term to which it can step.
We can define this in Coq as follows:

```code
Definition normal_form (t : tm) : Prop :=
  ~ exists t', eval t t'.
```

### Exercises

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
begins initially with one goal (the statement of the lemma you are tying to
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
backward reasoning in this tutorial. Of course, most people naturally a
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

In the following example, our proof script will build a value corresponding to
the following proof tree:

```
                        nvalue t
             ---------------------------- (e_predsucc)
             eval (tm_pred (tm_succ t)) t
    ------------------------------------------------ (e_succ)
    eval (tm_succ (tm_pred (tm_succ t))) (tm_succ t)
```

Step through every cell below to see how this tree is constructed.

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

You can see below that there is no magic happening at this point:
`e_succ_pred_succ` is a value that can be used like any other value we have seen
so far. We can ask Coq for its type:

```code
Check e_succ_pred_succ.
```

And we can see the value we have constructed with tactics:

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

#### Example 3

Any tactic like `apply` that takes the name of a constructor or lemma as an
argument can just as easily be given a more complicated expression as an
argument. Thus, we may use function application to construct proof objects on
the fly in these cases. Observe how this technique can be used to rewrite the
proof of the previous lemma.

Although, we have eliminated one use of `apply`, this is not necessarily an
improvement over the previous proof. However, there are cases where this
technique is quite valuable.

``` code
Lemma m_succ_pred_succ_alt : forall t,
  nvalue t ->
  eval_many (tm_succ (tm_pred (tm_succ t))) (tm_succ t).
Proof.
  intros t Hn.
```

```code
  Check m_step.
  apply (m_step
         (tm_succ (tm_pred (tm_succ t)))
         (tm_succ t)
         (tm_succ t)
        ).
```

```code
    Check e_succ_pred_succ.
    apply (e_succ_pred_succ t Hn).
```

```code
    apply t.
```

```code
    Check m_refl.
    apply (m_refl (tm_succ t)).
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

### Working with Definitions

```
    - [unfold]
```


There is a notion of equivalence on Coq terms that arises from the conversion
rules of the underlying calculus of constructions. It is sometimes useful to be
able to replace one term in a proof with an equivalent one. For instance, we may
want to replace a defined name with its definition. This sort of replacement can
be done the tactic `unfold`. This tactic can be used to manipulate the goal or
the hypotheses.

``` code
Definition strongly_diverges t :=
  forall u, eval_many t u -> ~ normal_form u.
```

``` code
Lemma unfold_example : forall t t',
  strongly_diverges t ->
  eval t t' ->
  strongly_diverges t'.
Proof.
  intros t t' Hd He.
   unfold strongly_diverges. intros u Hm.
   unfold strongly_diverges in Hd.
   apply Hd. apply m_step with (t' := t').
    apply He.
    apply Hm.
Qed.
```


**Exercise** In reality, many tactics will perform conversion automatically as necessary. Try
removing the uses of `unfold` from the above proof to check which ones were
necessary.


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

**Example** If the goal is a disjunction, we can use the `left` or `right`
tactics to solve it by proving the left or right side of the conclusion.
 
``` code
Lemma true_and_succ_zero_values :
  value tm_true /\ value (tm_succ tm_zero).
Proof.
  unfold value. split.
    left. apply b_true.
    right. apply n_succ. apply n_zero.
Qed.
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

#### Lab 2

Work on the following exercise.

**Exercise**

``` code
Lemma two_values : forall t u,
  value t /\ value u ->
    bvalue t \/
    bvalue u \/
    (nvalue t /\ nvalue u).
```

``` code
  (** We know [value t] and [value u], which means either
      [bvalue t] or [nvalue t], and either [bvalue u] or
      [nvalue u].  Consider the case in which
      [bvalue t] holds. Then one of the disjuncts of our
      conclusion is proved.  Next, consider the case in which
      [nvalue t] holds.  Now consider the subcase where
      [bvalue u] holds. ... *)
Proof.
```

``` code
  (* to finish *)
Admitted.
```

**Example** `destruct` can be used on propositions with implications. This will
have the effect of performing `destruct` on the conclusion of the implication,
while leaving the hypotheses of the implication as additional subgoals.
 
``` code
Lemma destruct_example : forall bv t t' t'',
  bvalue bv ->
  (value bv -> eval t t' /\ eval t' t'') ->
  eval_many t t''.
Proof.
  intros bv t t' t'' Hbv H. destruct H as [ H1 H2 ].
    Show 2.
    unfold value. left. apply Hbv.
    apply m_two with (t2 := t').
      apply H1.
      apply H2.
Qed.
```

**Tip** After applying a tactic that introduces multiple subgoals, it is
sometimes useful to see not only the subgoals themselves but also their
hypotheses. Adding the command `Show n.` to your proof script to cause Coq to
display the nth subgoal in full.
 

## Reasoning by Cases and Induction

``` code
    - [destruct] (for inductively defined propositions)
    - [induction]
```

**Example** Use `destruct` to reason by cases on an inductively defined datatype
or proposition.

Note: It is possible to supply `destruct` with a pattern in these instances
also. However, the patterns become increasingly complex for bigger inductive
definitions; so it is often more practical to omit the pattern (thereby letting
Coq choose the names of the terms and hypotheses in each case), in spite of the
fact that this adds an element of fragility to the proof script (since the proof
script will mention names that were system-generated).
 
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

**Example** It is possible to use `destruct` not just on hypotheses but on any
lemma we have proved. If we have a lemma
 

```
      lemma1 : P /\ Q
```

then we can use the tactic

```
      destruct lemma1 as [ H1 H2 ].
```

to continue our proof with `H1 : P` and `H2 : Q` in our context. This works even
if the lemma has antecedents (they become new subgoals); however it fail if the
lemma has a universal quantifier, such as this:

```
      lemma2 : forall x, P(x) /\ Q(x)
```

However, remember that we can build a proof of `P(e) /\ Q(e)` (which can be
destructed) using the Coq expression `lemma2 e`. So we need to phrase our tactic
as

```
      destruct (lemma2 e) as [ H1 H2 ].
```

An example of this technique is below.

``` code
Lemma m_iszero_nvalue : forall t v,
  nvalue v ->
  eval_many t v ->
  eval_many (tm_iszero t) tm_true \/
  eval_many (tm_iszero t) tm_false.
Proof.
  intros t v Hnv Hm.
   destruct (e_iszero_nvalue v) as [ H1 | H2 ].
    apply Hnv.
    left. apply m_trans with (t' := tm_iszero v).
      apply m_iszero. apply Hm.
      apply m_one. apply H1.
    right. apply m_trans with (t' := tm_iszero v).
      apply m_iszero. apply Hm.
      apply m_one. apply H2.
Qed.
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

## Working with Existential Quantification

``` code
    - [exists]
    - [destruct] (for existential propositions)
```

**Example** Use `exists` to give the witness for an existential quantifier in
your goal.
 
``` code
Lemma if_bvalue : forall t1 t2 t3,
  bvalue t1 ->
  exists u, eval (tm_if t1 t2 t3) u.
Proof.
  intros t1 t2 t3 Hb. destruct Hb.
    exists t2. apply e_iftrue.
    exists t3. apply e_iffalse.
Qed.
```

**Example** You may use `destruct` to break open an existential hypothesis.
 
``` code
Lemma m_two_exists : forall t u,
  (exists w, eval t w /\ eval w u) ->
  eval_many t u.
Proof.
  intros t u H.
   destruct H as [ w He ].
   destruct He as [ He1 He2 ].
   apply m_two with (t2 := w).
    apply He1.
    apply He2.
Qed.
```

**Example** Tip: We can combine patterns that destruct existentials with
patterns that destruct other logical connectives.

Here is the same proof with just one use of `destruct`.
 
``` code
Lemma m_two_exists' : forall t u,
  (exists w, eval t w /\ eval w u) ->
  eval_many t u.
Proof.
  intros t u H. destruct H as [ w [ He1 He2 ] ].
   apply m_two with (t2 := w).
    apply He1.
    apply He2.
Qed.
```

**Example** Tip: We give patterns to the `intros` tactic to destruct hypotheses
as we introduce them.

Here is the same proof again without any uses of `destruct`.
 
``` code
Lemma m_two_exists'' : forall t u,
  (exists w, eval t w /\ eval w u) ->
  eval_many t u.
Proof.
  intros t u [ w [ He1 He2 ] ].
   apply m_two with (t2 := w).
    apply He1.
    apply He2.
Qed.
```

**Exercise**

``` code
Lemma value_can_expand : forall v,
  value v ->
  exists u, eval u v.
Proof.
  (* to finish *)
Admitted.
```

#### Lab 4
    Work on the following exercise.

**Exercise** Tip: You should find the lemma `m_iszero` useful. Use `Check
m_iszero.` if you've forgotten its statement.
 
``` code
Lemma exists_iszero_nvalue : forall t,
  (exists nv, nvalue nv /\ eval_many t nv) ->
  exists bv, eval_many (tm_iszero t) bv.
Proof.
  (** There exists some [nv] such that [nvalue nv].  Consider
      the case where [nv] is [tm_zero].  Then choose [bv] to
      be [tm_true].  By [m_trans], we can show that
      [eval_many (tm_iszero t) tm_true] by showing
      [eval_many (tm_iszero t) (tm_iszero tm_zero)] and
      [eval_many (tm_iszero tm_zero) tm_true].  The former
      follows from [m_iszero] and our assumption.  The latter
      follows from [m_one] and the rule [e_iszerozero].  On the
      other hand, in the case where [nv] is built from
      [tm_succ], we choose [bv] to be [tm_false] and the proof
      follows similarly. *)

  (* to finish *)
Admitted.
```

## Working with Negation

``` code
    - [unfold not]
    - [destruct] (for negation)
```

**Example** The standard library defines an uninhabited type `False` and defines
`not P` to stand for `P -> False`. Furthermore, Coq defines the notation `~ P`
to stand for `not P`. (Such notations only affect parsing and printing -- Coq
views `not P` and `~ P` as being syntactically equal.)

The most basic way to work with negated statements is to unfold `not` and treat
`False` just as any other proposition.

(Note how multiple definitions can be unfolded with one use of `unfold`. Also,
as noted earlier, many uses of `unfold` are not strictly necessary. You can try
deleting the uses from the proof below to check that the proof script still
works.)
 
``` code
Lemma normal_form_succ : forall t,
  normal_form (tm_succ t) ->
  normal_form t.
Proof.
  intros t Hnf.
   unfold normal_form. unfold not.
   unfold normal_form, not in Hnf.
   intros [ t' H' ]. apply Hnf.
   exists (tm_succ t'). apply e_succ. apply H'.
Qed.
```

**Exercise**
 
``` code
Lemma normal_form_to_forall : forall t,
  normal_form t ->
  forall u, ~ eval t u.
Proof.
  (* to finish *)
Admitted.
```

**Exercise**
    
``` code
Lemma normal_form_from_forall : forall t,
  (forall u, ~ eval t u) ->
  normal_form t.
Proof.
  (* to finish *)
Admitted.
```

**Example** If you happen to have `False` as a hypothesis, you may use
`destruct` on that hypothesis to solve your goal.
 
``` code
Lemma False_hypothesis : forall v,
  False ->
  value v.
Proof.
  intros v H. destruct H.
Qed.
```

**Example** Recalling that `destruct` can be used on propositions with
antecedents and that negation is simply an abbreviation for an implication,
using `destruct` on a negated hypothesis has the derived behavior of replacing
our goal with the proposition that was negated in our context.

Tip: We actually don't even need to do the unfolding below because `destruct`
would have done it for us.
 
``` code
Lemma destruct_negation_example : forall t v,
  value v ->
  eval t tm_zero ->
  (value v -> normal_form t) ->
  eval tm_true tm_false.
Proof.
  intros t v Hnv He Hnf.
   unfold normal_form, not in Hnf.
  (* As usual, unfolding was optional here. *)
   destruct Hnf.
    apply Hnv.
    exists tm_zero. apply He.
Qed.
```

**Exercise** This one may be a bit tricky. Start by using `destruct` on one of
your hypotheses.
 
``` code
Lemma negation_exercise : forall v1 v2,
  ~ (value v1 \/ value v2) ->
  ~ (~ bvalue v1 /\ ~ bvalue v2) ->
  eval tm_true tm_false.
Proof.
  (* to finish *)
Admitted.
```


## Working with Equality

``` code
    - [reflexivity]
    - [subst]
    - [rewrite]
    - [inversion] (on equalities)
```

**Example** If you have an equality in your context, there are several ways to
substitute one side of the equality for the other in your goal or in other
hypotheses.

If one side of the equality is a variable `x`, then the tactic `subst x` will
replace all occurrences of `x` in the context and goal with the other side of
the quality and will remove `x` from your context.

Use `reflexivity` to solve a goal of the form `e = e`.
 
``` code
Lemma equality_example_1 : forall t1 t2 t3 u1 u2,
  t1 = tm_iszero u1 ->
  t2 = tm_succ u2 ->
  t3 = tm_succ t2 ->
  tm_if t1 t2 t3 =
    tm_if (tm_iszero u1) (tm_succ u2) (tm_succ (tm_succ u2)).
Proof.
  intros t1 t2 t3 u1 u2 Heq1 Heq2 Heq3.
   subst t1. subst t2. subst t3. reflexivity.
Qed.
```

**Example** If neither side of the equality in your context is a variable (or if
you don't want to discard the hypothesis), you can use the `rewrite` tactic to
perform a substitution. The arrow after `rewrite` indicates the direction of the
substitution. As demonstrated, you may perform rewriting in the goal or in a
hypothesis.
 
``` code
Lemma equality_example_2a : forall t u v,
  tm_succ t = tm_succ u ->
  eval (tm_succ u) v ->
  eval (tm_succ t) v.
Proof.
  intros t u v Heq He. rewrite -> Heq. apply He.
Qed.
```

``` code
Lemma equality_example_2b : forall t u v,
  tm_succ t = tm_succ u ->
  eval (tm_succ u) v ->
  eval (tm_succ t) v.
Proof.
  intros t u v Heq He. rewrite <- Heq in He. apply He.
Qed.
```

**Example** We also note that, analogously with `destruct`, we may use `rewrite`
even with a hypothesis (or lemma) that has antecedents.
 
``` code
Lemma equality_example_2c : forall t u v,
  nvalue v ->
  (nvalue v -> tm_succ t = tm_succ u) ->
  eval (tm_succ u) v ->
  eval (tm_succ t) v.
Proof.
  intros t u v Hnv Heq He. rewrite <- Heq in He.
    apply He.
    apply Hnv.
Qed.
```

**Example** If you need to derive additional equalities implied by an equality
in your context (e.g., by the principle of constructor injectivity), you may use
`inversion`. `inversion` is a powerful tactic that uses unification to introduce
more equalities into your context. (You will observe that it also performs some
substitutions in your goal.)
 
``` code
Lemma equality_example_3 : forall t u,
  tm_succ t = tm_succ u ->
  t = u.
Proof.
  intros t u Heq. inversion Heq. reflexivity.
Qed.
```

**Exercise**

``` code
Lemma equality_exercise : forall t1 t2 t3 u1 u2 u3 u4,
  tm_if t1 t2 t3 = tm_if u1 u2 u2 ->
  tm_if t1 t2 t3 = tm_if u3 u3 u4 ->
  t1 = u4.
Proof.
  (* to finish *)
Admitted.
```

**Example** `inversion` will also solve a goal when unification fails on a
hypothesis. (Internally, Coq can construct a proof of `False` from contradictory
equalities.)
 
``` code
Lemma equality_example_4 :
  tm_zero = tm_true ->
  eval tm_true tm_false.
Proof.
  intros Heq. inversion Heq.
Qed.
```

#### Lab 5

Work on `equality_exercise` above and `succ_not_circular` below.

**Exercise** Note: `e1 <> e2` is a notation for `~ e1 = e2`, i.e., the two are
treated as syntactically equal.

Note: This is fairly trivial to prove if we have a size function on terms and
some automation. With just the tools we have described so far, it requires just
a little bit of work.

Hint: The proof requires induction on `t`. (This is the first example of
induction on datatypes, but it is even more straightforward than induction on
propositions.) In each case, unfold the negation, pull the equality into the
context, and use `inversion` to eliminate contradictory equalities.
 
``` code
Lemma succ_not_circular : forall t,
  t <> tm_succ t.
Proof.
  (* to finish *)
Admitted.
```

## Reasoning by Inversion

``` code
    - [inversion] (on propositions)
```

**Example** The `inversion` tactic also allows you to reason by inversion on an
inductively defined proposition as in paper proofs: we try to match some
proposition with the conclusion of each inference rule and only consider the
cases (possibly none) where there is a successful unification. In those cases,
we may use the premises of the inference rule in our reasoning.

Since `inversion` may generate many equalities between variables, it is useful
to know that using `subst` without an argument will perform all possible
substitutions for variables. It is a little difficult to predict which variables
will be eliminated and which will be kept by this tactic, but this is a typical
sort of trade-off when using powerful tactics.

(The use of `subst` in this proof is superfluous, but you can observe that it
simplifies the context.)
 
``` code
Lemma value_succ_nvalue : forall t,
  value (tm_succ t) ->
  nvalue t.
Proof.
  intros t H. unfold value in H. destruct H as [ H1 | H2 ].
  (* No unification is possible -- [inversion] solves goal. *)
    inversion H1.
  (* Just the [n_succ] cases unifies with H2. *)
    inversion H2. subst. apply H0.
Qed.
```

#### Lab 6

Work on the exercise below.


**Exercise**

``` code
Lemma inversion_exercise : forall t,
  normal_form t ->
  eval_many (tm_pred t) tm_zero ->
  nvalue t.
Proof.
  (** By inversion on the [eval_many] relation, then conclusion
      [eval_many (tm_pred t) tm_zero] must have been derived by
      the rule [m_step], which means there is some [t'] for
      which [eval (tm_pred t) t'] and [eval_many t' tm_zero].
      Now, by inversion on the [eval] relation, there are only
      three ways that [eval (tm_pred t) t'] could have been
      derived:
      * By [e_predzero], with [t] and [t'] both being equal to
        [tm_zero].  Our conclusion follows from [n_zero].
      * By [e_predsucc], with [t] being [tm_succ t0] where we
        have [nvalue t0].  In this case, our conclusion is
        provable with [n_succ].
      * By [e_pred], with [t] taking an evaluation step.  This
        contradicts our assumption that [t] is a normal form
        (which can be shown by using [destruct] on that
        assumption). *)

  (* to finish *)
Admitted.
```

**Exercise** Tip: Nested patterns will be useful here.
 
``` code
Lemma contradictory_equalities_exercise :
  (exists t, exists u, exists v,
    value t /\
    t = tm_succ u /\
    u = tm_pred v) ->
  eval tm_true tm_false.
Proof.
  (* to finish *)
Admitted.
```

**Exercise**

``` code
Lemma eval_fact_exercise : forall t1 t2,
  eval (tm_iszero (tm_pred t1)) t2 ->
  eval t2 tm_false ->
  exists u, t1 = tm_succ u.
Proof.
  (* to finish *)
Admitted.
```

**Exercise**

``` code
Lemma normal_form_if : forall t1 t2 t3,
  normal_form (tm_if t1 t2 t3) ->
  t1 <> tm_true /\ t1 <> tm_false /\ normal_form t1.
Proof.
  (* to finish *)
Admitted.
```

## Additional Important Tactics

``` code
    - [generalize dependent]
    - [assert]
    - [;]
    - [clear]
```

**Example** Sometimes we need to have a tactic that moves hypotheses from our
context back into our goal. Often this is because we want to perform induction
in the middle of a proof and will not get a sufficiently general induction
hypothesis without a goal of the correct form. (To be specific, if we need to
have an induction hypothesis with a `forall` quantifier in front, then we must
make sure our goal has a `forall` quantifier in front at the time we invoke the
`induction` tactic.) Observe how `generalize dependent` achieves this in the
proof below, moving the variable `t` and all dependent hypotheses back into the
goal. You may want to remove the use of `generalize dependent` to convince
yourself that it is performing an essential role here.
 
``` code
Lemma value_is_normal_form : forall v,
  value v ->
  normal_form v.
Proof.
  intros v [ Hb | Hn ] [ t He ].
    destruct Hb.
      inversion He.
      inversion He.
    generalize dependent t. induction Hn.
      intros t He. inversion He.
      intros u He. inversion He. subst. destruct (IHHn t').
       apply H0.
Qed.
```

**Exercise** Coq has many operations (called "tacticals") to combine smaller
tactics into larger ones.

If `t1` and `t2` are tactics, then `t1; t2` is a tactic that executes `t1`, and
then executes `t2` on subgoals left by or newly generated by `t1`. This can help
to eliminate repetitious use of tactics. Two idiomatic uses are performing
`subst` after `inversion` and performing `intros` after `induction`. More
opportunities to use this tactical can usually be discovered after writing a
proof. (It is worth noting that some uses of this tactical can make proofs less
readable or more difficult to maintain. Alternatively, some uses can make proofs
more readable or easier to maintain. It is always good to think about your
priorities when writing a proof script.)

Revise the proof for `value_is_normal_form` to include uses of the `;` tactical.
 

**Example** Sometimes it is helpful to be able to use forward reasoning in a
proof. One form of forward reasoning can be done with the tactic `assert`.
`assert` adds a new hypothesis to the context but asks us to first justify it.
 
``` code
Lemma nvalue_is_normal_form : forall v,
  nvalue v ->
  normal_form v.
Proof.
  intros v Hnv.
   assert (value v) as Hv. right. apply Hnv.
   apply value_is_normal_form. apply Hv.
Qed.
```

**Example** `assert` can also be supplied with a tactic that proves the
assertion. We rewrite the above proof using this form.
 
``` code
Lemma nvalue_is_normal_form' : forall v,
  nvalue v ->
  normal_form v.
Proof.
  intros v Hnv.
   assert (value v) as Hv by (right; apply Hnv).
   apply value_is_normal_form. apply Hv.
Qed.
```

**Example** The proof below introduces two new, simple tactics. First, the
tactic `replace e1 with e2` performs a substitution in the goal and then
requires that you prove `e2 = e1` as a new subgoal. This often allows us to
avoid more cumbersome forms of forward reasoning. Second, the `clear` tactic
discards a hypothesis from the context. Of course, this tactic is never needed,
but it can be nice to use when there are complicated, irrelevant hypotheses in
the context.
 
``` code
Lemma single_step_to_multi_step_determinacy :
  (forall t u1 u2, eval t u1 -> eval t u2 -> u1 = u2) ->
  forall t v1 v2,
    eval_many t v1 -> normal_form v1 ->
    eval_many t v2 -> normal_form v2 ->
    v1 = v2.
Proof.
  intros H t v1 v2 Hm1 Hnf1 Hm2 Hnf2. induction Hm1.
    clear H. destruct Hm2.
      reflexivity.
      destruct Hnf1. exists t'. apply H.
    destruct Hm2.
      destruct Hnf2. exists t'. apply H0.
      apply IHHm1; clear IHHm1.
        apply Hnf1.
        replace t' with t'0.
          apply Hm2.
          apply H with (t := t).
            apply H1.
            apply H0.
Qed.
```

**Exercise** This proof is lengthy and thus somewhat challenging. All of the
techniques from this section will be useful; some will be essential. In
particular, you will need to use `generalize dependent` at the beginning of the
proof. You will find `assert` helpful in the cases where your assumptions are
contradictory but none of them are in a negative form. In that situation, you
can assert a negative statement that follows from your hypotheses (recall that
`normal_form` is a negative statement). Finally, you will want to use the above
lemma `nvalue_is_normal_form`. Good luck!
 
``` code
Theorem eval_deterministic : forall t t' t'',
  eval t t' ->
  eval t t'' ->
  t' = t''.
Proof.
  (* to finish *)
Admitted.
```

**Exercise** Prove the following lemmas. The last is quite long, and you may
wish to wait until you know more about automation.

```
Lemma full_eval_from_value : forall v w,
  value v ->
  full_eval v w ->
  v = w.

Lemma eval_full_eval : forall t t' v,
  eval t t' ->
  full_eval t' v ->
  full_eval t v.

Lemma full_eval_complete : forall t v,
  value v ->
  eval_many t v ->
  full_eval t v.
```

## Basic Automation

``` code
  - [eapply], [esplit]
  - [auto], [eauto]
```

**Example** You can use `eapply e` instead of `apply e with (x := e1)`. This
will generate subgoals containing unification variables that will get unified
during subsequent uses of `apply`.
 
``` code
Lemma m_if : forall t1 u1 t2 t3,
  eval_many t1 u1 ->
  eval_many (tm_if t1 t2 t3) (tm_if u1 t2 t3).
Proof.
  intros t1 u1 t2 t3 Hm. induction Hm.
    apply m_refl.
    eapply m_step.
      apply e_if. apply H.
      apply IHHm.
Qed.
```

**Example** You can use `esplit` to turn an existentially quantified variable in
your goal into a unification variable.
 
``` code
Lemma exists_pred_zero :
  exists u, eval (tm_pred tm_zero) u.
Proof.
  esplit. apply e_predzero.
Qed.
```

**Example** The `auto` tactic solves goals that are solvable by any combination
of

- `intros`
- `apply` (used on some local hypothesis)
- `split`, `left`, `right`
- `reflexivity`

If `auto` cannot solve the goal, it will leave the proof state completely
unchanged (without generating any errors).

The lemma below is a proposition that has been contrived for the sake of
demonstrating the scope of the `auto` tactic and does not say anything of
practical interest. So instead of thinking about what it means, you should think
about the operations that `auto` had to perform to solve the goal.

Note: It is important to remember that `auto` does not destruct hypotheses!
There are more advanced forms of automation available that do destruct
hypotheses in some specific ways.
 
``` code
Lemma auto_example : forall t t' t'',
  eval t t' ->
  eval t' t'' ->
  (forall u, eval t t' -> eval t' u -> eval_many t u) ->
  eval t' t \/ t = t /\ eval_many t t''.
Proof.
  auto.
Qed.
```

**Example** The `eauto` tactic solves goals that are solvable by some
combination of

- `intros` 
- `eapply` (used on some local hypothesis)
- `split`, `left`, `right` 
- `esplit`
- `reflexivity` 

lemma has two significantly differences from the previous one, both of which
render `auto` useless.
 
``` code
Lemma eauto_example : forall t t' t'',
  eval t t' ->
  eval t' t'' ->
  (forall u, eval t u -> eval u t'' -> eval_many t t'') ->
  eval t' t \/ (exists u, t = u) /\ eval_many t t''.
Proof.
  eauto.
Qed.
```

**Example** You can enhance `auto` (or `eauto`) by appending `using x_1, ...,
x_n`, where each `x_i` is the name of some constructor or lemma. Then `auto`
will attempt to apply those constructors or lemmas in addition to the
assumptions in the local context.
 
``` code
Lemma eauto_using_example : forall t t' t'',
  eval t t' ->
  eval t' t'' ->
  eval t' t \/ t = t /\ eval_many t t''.
Proof.
  eauto using m_step, m_one.
Qed.
```

#### Lab 7

**Exercise** Go back and rewrite your proofs for `m_one`, `m_two`, and
`m_iftrue_step`. You should be able to make them very succinct given what you
know now.
 

**Exercise** See how short you can make these proofs.

Note: This is an exercise. We are not making the claim that shorter proofs are
necessarily better!

Hint: Remember that we can connect tactics in sequence with `;`. However, as you
can imagine, figuring out the best thing to write after a `;` usually involves
some trial and error.
 
``` code
Lemma pred_not_circular : forall t,
  t <> tm_pred t.
Proof.
  (* to finish *)
Admitted.
```

``` code
Lemma m_succ : forall t u,
  eval_many t u ->
  eval_many (tm_succ t) (tm_succ u).
Proof.
  (* to finish *)
Admitted.
```

``` code
Lemma m_pred : forall t u,
  eval_many t u ->
  eval_many (tm_pred t) (tm_pred u).
Proof.
  (* to finish *)
Admitted.
```

**Exercise** Go back and rewrite your proofs for `m_trans` and `two_values`.
Pulling together several tricks you've learned, you should be able to prove
`two_values` in one (short) line. Since this is a notebook, the easiest way for
you to do that may be to copy the cells here.
 

**Note** Sometimes there are lemmas or constructors that are so frequently
needed by `auto` that we don't want to have to add them to our `using` clause
each time. Coq allows us to request that certain propositions that always be
considered by `auto` and `eauto`.

The following command adds four lemmas to the default search procedure of
`auto`.
 
``` code
Hint Resolve m_if m_succ m_pred m_iszero.
```

Constructors of inductively defined propositions are some of the most frequently
needed by `auto`. Instead of writing

```
    Hint Resolve b_true b_false.
```

we may simply write

```
    Hint Constructors bvalue.
```

Let's add all our constructors to `auto`.

``` code
Hint Constructors bvalue nvalue eval eval_many.
```

By default `auto` will never try to unfold definitions to see if a lemma or
constructor can be applied. With the `Hint Unfold` command, we can instruct
`auto` to try unfold definitions in the goal as it is working.

``` code
Hint Unfold value normal_form.
```

There are a few more variants on the `Hint` command that can be used to further
customize `auto`. You can learn about them in the Coq reference manual.

## Functions and Conversion

``` code
    - [Fixpoint/struct]
    - [match ... end]
    - [if ... then ... else ...]
    - [simpl]
    - [remember]
```

In this section we start to use Coq as a programming language and learn how to
reason about programs defined within Coq.

**Example** Coq defines many datatypes in its standard libraries. Have a quick
look now through the library `Datatypes` to see some of the basic ones, in
particular `bool` and `nat`. (Note that constructors of the datatype `nat` are
the letter `O` and the letter `S`. However, Coq will parse and print `nat`s
using a standard decimal representation.)

We define two more datatypes here that will be useful later.
 
``` code
Inductive bool_option : Set :=
| some_bool : bool -> bool_option
| no_bool : bool_option.
```

``` code
Inductive nat_option : Set :=
| some_nat : nat -> nat_option
| no_nat : nat_option.
```

**Example** We can define simple (non-recursive) functions from one datatype to
another using the `Definition` keyword. The `match` construct allows us to do
case analysis on a datatype. The `match` expression has a first-match semantics
and allows nested patterns; however, Coq's type checker demands that
pattern-matching be exhaustive.

We define functions below for converting between Coq `bool`s and boolean values
in our object language.
 
``` code
Definition tm_to_bool (t : tm) : bool_option :=
  match t with
  | tm_true => some_bool true
  | tm_false => some_bool false
  | _ => no_bool
  end.
```

``` code
Definition bool_to_tm (b : bool) : tm :=
  match b with
  | true => tm_true
  | false => tm_false
  end.
```

**Example** Coq also has an `if/then/else` expression. It can be used, not just
with the type `bool` but, in fact, with any datatype having exactly two
constructors (the first constructor corresponding to the `then` branch and the
second to the `else` branch). Thus, we can define a function `is_bool` as below.
 
``` code
Definition is_bool (t : tm) : bool :=
  if tm_to_bool t then true else false.
```

**Example** To define a recursive function, use `Fixpoint` instead of
`Definition`.

The type system will only allow us to write functions that terminate. The
annotation `{struct t}` here informs the type-checker that termination is
guaranteed because the function is being defined by structural recursion on `t`.
 
``` code
Fixpoint tm_to_nat (t : tm) {struct t} : nat_option :=
  match t with
  | tm_zero => some_nat O
  | tm_succ t1 =>
      match tm_to_nat t1 with
      | some_nat n => some_nat (S n)
      | no_nat => no_nat
      end
  | _ => no_nat
  end.

Fixpoint nat_to_tm (n : nat) {struct n} : tm :=
  match n with
  | O => tm_zero
  | S m => tm_succ (nat_to_tm m)
  end.
```

**Exercise** Write a function `interp : tm -> tm` that returns the normal form
of its argument according to the small-step semantics given by `eval`.

Hint: You will want to use `tm_to_nat` (or another auxiliary function) to
prevent stuck terms from stepping in the cases `e_predsucc` and `e_iszerosucc`.
 

**Example** The tactic `simpl` (recursively) reduces the application of a
function defined by pattern-matching to an argument with a constructor at its
head. You can supply `simpl` with a particular expression if you want to prevent
it from simplifying elsewhere.
 
``` code
Lemma bool_tm_bool : forall b,
  tm_to_bool (bool_to_tm b) = some_bool b.
Proof.
  intros b. destruct b.
    simpl (bool_to_tm true). simpl. reflexivity.
    (* It turns out that [simpl] is unnecessary above, since
       [reflexivity] can automatically check that two terms are
       convertible. *)
    reflexivity.
Qed.
```

**Example** We can also apply the tactic `simpl` in our hypotheses.
 
``` code
Lemma tm_bool_tm :forall t b,
  tm_to_bool t = some_bool b ->
  bool_to_tm b = t.
Proof.
  intros t b Heq. destruct t.
    simpl in Heq. inversion Heq.
     simpl. reflexivity.
    (* As with [reflexivity], [inversion] can automatically
       perform reduction on terms as necessary, so the above use
       of [simpl] was optional. *)
    inversion Heq. reflexivity.
    simpl in Heq. inversion Heq.
    (* Again, the above use of [simpl] was optional. *)
    inversion Heq.
    inversion Heq.
    inversion Heq.
    inversion Heq.
Qed.
```

**Exercise**

``` code
Lemma tm_to_bool_dom_includes_bvalue : forall bv,
  bvalue bv -> exists b, tm_to_bool bv = some_bool b.
Proof.
  (* to finish *)
Admitted.
```

**Exercise**

``` code
Lemma tm_to_bool_dom_only_bvalue : forall bv b,
  tm_to_bool bv = some_bool b -> bvalue bv.
Proof.
  (* to finish *)
Admitted.
```

**Example** Not all uses of `simpl` are optional. Sometimes they are necessary
so that we can use the `rewrite` tactic. Observe, also, how using `rewrite` can
automatically trigger a reduction if it creates a redex.
 
``` code
Lemma nat_tm_nat : forall n,
  tm_to_nat (nat_to_tm n) = some_nat n.
Proof.
  intros n. induction n.
    reflexivity.
    simpl. rewrite -> IHn. reflexivity.
Qed.
```

**Example** Here's an example where it is necessary to use `simpl` on a
hypothesis. To trigger a reduction of a `match` expression in a hypothesis, we
use the `destruct` tactic on the expression being matched.
 
``` code
Lemma tm_nat_tm : forall t n,
  tm_to_nat t = some_nat n ->
  nat_to_tm n = t.
Proof.
  intros t. induction t; intros n Heq.
    inversion Heq.
    inversion Heq.
    inversion Heq.
    inversion Heq. reflexivity.
    simpl in Heq. destruct (tm_to_nat t).
      inversion Heq. simpl. rewrite -> IHt.
        (* Note how we may use [rewrite] even on an equation
           that is preceded by some other hypotheses. *)
        reflexivity.
        reflexivity.
      inversion Heq.
    inversion Heq.
    inversion Heq.
Qed.
```

**Exercise**

``` code
Lemma tm_to_nat_dom_includes_nvalue : forall v,
  nvalue v -> exists n, tm_to_nat v = some_nat n.
Proof.
  (* to finish *)
Admitted.
```

**Exercise**

``` code
Lemma tm_to_nat_dom_only_nvalue : forall v n,
  tm_to_nat v = some_nat n -> nvalue v.
Proof.
  (* to finish *)
Admitted.
```

**Example** Using the tactic `destruct` (or `induction`) on a complex expression
(i.e., one that is not simply a variable) may not leave you with enough
information for you to finish the proof. The tactic `remember` can help in these
cases. Its usage is demonstrated below. If you are curious, try to finish the
proof without `remember` to see what goes wrong.
 
``` code
Lemma remember_example : forall v,
  eval_many
    (tm_pred (tm_succ v))
    (match tm_to_nat v with
      | some_nat _ => v
      | no_nat => tm_pred (tm_succ v)
     end).
Proof.
  intros v. remember (tm_to_nat v) as x. destruct x.
    apply m_one. apply e_predsucc.
     eapply tm_to_nat_dom_only_nvalue.
     rewrite <- Heqx. reflexivity.
    apply m_refl.
Qed.
```

**Exercise** Prove the following lemmas involving the function `interp` from a
previous exercise:

```
Lemma interp_reduces : forall t,
  eval_many t (interp t).

Lemma interp_fully_reduces : forall t,
  normal_form (interp t).
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

Lemma value_can_expand_sol : forall v,
  value v ->
  exists u, eval u v.
Proof.
  intros v Hv. exists (tm_if tm_true v v). apply e_iftrue.
Qed.

Lemma exists_iszero_nvalue_sol : forall t,
  (exists nv, nvalue nv /\ eval_many t nv) ->
  exists bv, eval_many (tm_iszero t) bv.
Proof.
  intros t [ nv [ Hnv Hm ]]. destruct Hnv.
    exists tm_true.
     apply m_trans with (t' := tm_iszero tm_zero).
      apply m_iszero. apply Hm.
      apply m_one. apply e_iszerozero.
    exists tm_false.
     apply m_trans with (t' := tm_iszero (tm_succ t0)).
      apply m_iszero. apply Hm.
      apply m_one. apply e_iszerosucc. apply Hnv.
Qed.

Lemma normal_form_to_forall_sol : forall t,
  normal_form t ->
  forall u, ~ eval t u.
Proof.
  unfold normal_form, not. intros t H u He.
   apply H. exists u. apply He.
Qed.

Lemma normal_form_from_forall_sol : forall t,
  (forall u, ~ eval t u) ->
  normal_form t.
Proof.
  unfold normal_form, not. intros t H [ t' Het' ].
   apply H with (u := t'). apply Het'.
Qed. 

Lemma negation_exercise_sol : forall v1 v2,
  ~ (value v1 \/ value v2) ->
  ~ (~ bvalue v1 /\ ~ bvalue v2) ->
  eval tm_true tm_false.
Proof.
  intros v1 v2 H1 H2. destruct H2.
    split.
      intros Hb. destruct H1. left. left. apply Hb.
      intros Hb. destruct H1. right. left. apply Hb.
Qed.

Lemma equality_exercise_sol : forall t1 t2 t3 u1 u2 u3 u4,
  tm_if t1 t2 t3 = tm_if u1 u2 u2 ->
  tm_if t1 t2 t3 = tm_if u3 u3 u4 ->
  t1 = u4.
Proof.
  intros t1 t2 t3 u1 u2 u3 u4 Heq1 Heq2.
       inversion Heq1. subst t1. subst t2. subst t3.
       inversion Heq2. reflexivity.
Qed.

Lemma succ_not_circular_sol : forall t,
  t <> tm_succ t.
Proof.
  intros t. induction t.
    intros Heq. inversion Heq.
    intros Heq. inversion Heq.
    intros Heq. inversion Heq.
    intros Heq. inversion Heq.
    intros Heq. inversion Heq. destruct IHt. apply H0.
    intros Heq. inversion Heq.
    intros Heq. inversion Heq.
Qed.

Lemma inversion_exercise_sol : forall t,
  normal_form t ->
  eval_many (tm_pred t) tm_zero ->
  nvalue t.
Proof.
  intros t Hnf Hm. inversion Hm. subst. inversion H.
    apply n_zero.
    apply n_succ. apply H2.
    destruct Hnf. exists t'0. apply H2.
Qed.

Lemma contradictory_equalities_exercise_sol :
  (exists t, exists u, exists v,
    value t /\
    t = tm_succ u /\
    u = tm_pred v) ->
  eval tm_true tm_false.
Proof.
  intros [ t [ u [ v [ [ Hb | Hn ] [ eq1 eq2 ] ] ] ] ].
    destruct Hb.
      inversion eq1.
      inversion eq1.
    destruct Hn.
      inversion eq1.
      inversion eq1. subst t. subst u. inversion Hn.
Qed.

Lemma eval_fact_exercise_sol : forall t1 t2,
  eval (tm_iszero (tm_pred t1)) t2 ->
  eval t2 tm_false ->
  exists u, t1 = tm_succ u.
Proof.
  intros t1 t2 He1 He2. inversion He1. subst t2.
   inversion He2. subst t'.
   inversion H0. exists (tm_succ t0). reflexivity.
Qed.

Lemma normal_form_if_sol : forall t1 t2 t3,
  normal_form (tm_if t1 t2 t3) ->
  t1 <> tm_true /\ t1 <> tm_false /\ normal_form t1.
Proof.
  intros t1 t2 t3 Hnf. destruct t1.
    destruct Hnf. exists t2. apply e_iftrue.
    destruct Hnf. exists t3. apply e_iffalse.
    split.
      intros Heq. inversion Heq.
      split.
        intros Heq. inversion Heq.
        intros [t' He]. destruct Hnf. exists (tm_if t' t2 t3).
         apply e_if. apply He.
    split.
      intros Heq. inversion Heq.
      split.
        intros Heq. inversion Heq.
        intros [t' He]. inversion He.
    split.
      intros Heq. inversion Heq.
      split.
        intros Heq. inversion Heq.
        intros [t' He]. destruct Hnf. exists (tm_if t' t2 t3).
         apply e_if. apply He.
    split.
      intros Heq. inversion Heq.
      split.
        intros Heq. inversion Heq.
        intros [t' He]. destruct Hnf. exists (tm_if t' t2 t3).
         apply e_if. apply He.
    split.
      intros Heq. inversion Heq.
      split.
        intros Heq. inversion Heq.
        intros [t' He]. destruct Hnf. exists (tm_if t' t2 t3).
         apply e_if. apply He.
Qed.

Lemma full_eval_from_value_sol : forall v w,
  value v ->
  full_eval v w ->
  v = w.
Proof.
  intros v w Hv Hf. induction Hf.
    reflexivity.
    destruct Hv as [ Hb | Hn ].
      inversion Hb.
      inversion Hn.
    destruct Hv as [ Hb | Hn ].
      inversion Hb.
      inversion Hn.
    rewrite -> IHHf.
      reflexivity.
      right. apply value_succ_nvalue. apply Hv.
    destruct Hv as [ Hb | Hn ].
      inversion Hb.
      inversion Hn.
    destruct Hv as [ Hb | Hn ].
      inversion Hb.
      inversion Hn.
    destruct Hv as [ Hb | Hn ].
      inversion Hb.
      inversion Hn.
    destruct Hv as [ Hb | Hn ].
      inversion Hb.
      inversion Hn.
Qed.

Lemma value_is_normal_form_sol : forall v,
  value v ->
  normal_form v.
Proof.
  intros v [ Hb | Hn ] [ t He ].
    destruct Hb; inversion He.
    generalize dependent t.
     induction Hn; intros u He; inversion He; subst.
      destruct (IHHn t'). apply H0.
Qed.

Theorem eval_deterministic_sol : forall t t' t'',
  eval t t' ->
  eval t t'' ->
  t' = t''.
Proof.
  intros t t' t'' He1. generalize dependent t''.
   induction He1; intros t'' He2; inversion He2; subst.
    reflexivity.
    inversion H3.
    reflexivity.
    inversion H3.
    inversion He1.
    inversion He1.
    rewrite -> (IHHe1 t1'0).
      reflexivity.
      apply H3.
    rewrite -> (IHHe1 t'0).
      reflexivity.
      apply H0.
    reflexivity.
    inversion H0.
    reflexivity.
    assert (normal_form (tm_succ t)) as Hnf.
      apply nvalue_is_normal_form. apply n_succ. apply H.
     destruct Hnf. exists t'. apply H1.
    inversion He1.
    assert (normal_form (tm_succ t'')) as Hnf.
      apply nvalue_is_normal_form. apply n_succ. apply H0.
     destruct Hnf. exists t'. apply He1.
    rewrite -> (IHHe1 t'0).
      reflexivity.
      apply H0.
    reflexivity.
    inversion H0.
    reflexivity.
    assert (normal_form (tm_succ t)) as Hnf.
      apply nvalue_is_normal_form. apply n_succ. apply H.
     destruct Hnf. exists t'. apply H1.
    inversion He1.
    assert (normal_form (tm_succ t0)) as Hnf.
      apply nvalue_is_normal_form. apply n_succ. apply H0.
     destruct Hnf. exists t'. apply He1.
    rewrite -> (IHHe1 t'0).
      reflexivity.
      apply H0.
Qed.

Lemma eval_full_eval_sol : forall t t' v,
  eval t t' ->
  full_eval t' v ->
  full_eval t v.
Proof.
  intros t t' v He. generalize dependent v. induction He.
    intros v Hf. apply f_iftrue.
      apply f_value. left. apply b_true.
      apply Hf.
    intros v Hf. apply f_iffalse.
      apply f_value. left. apply b_false.
      apply Hf.
    intros v Hf. inversion Hf.
      subst. inversion H.
        inversion H0.
        inversion H0.
      subst. apply f_iftrue.
        apply IHHe. apply H3.
        apply H4.
      subst. apply f_iffalse.
        apply IHHe. apply H3.
        apply H4.
    intros v Hf. inversion Hf.
      subst. apply f_succ.
        apply value_succ_nvalue. apply H.
        apply IHHe. apply f_value. right.
             apply value_succ_nvalue. apply H.
      subst. apply f_succ.
        apply H0.
        apply IHHe. apply H1.
    intros v Hf. inversion Hf. apply f_predzero.
         apply f_value. right. apply n_zero.
    intros v Hf. assert (t = v).
      apply full_eval_from_value_sol.
        right. apply H.
        apply Hf.
      subst v. apply f_predsucc.
        apply H.
        apply f_succ.
          apply H.
          apply Hf.
    intros v Hf. inversion Hf.
      subst. destruct H as [ Hb | Hn ].
        inversion Hb.
        inversion Hn.
      subst. apply f_predzero. apply IHHe. apply H0.
      subst. apply f_predsucc.
        apply H0.
        apply IHHe. apply H1.
    intros v Hf. inversion Hf. apply f_iszerozero.
         apply f_value. right. apply n_zero.
    intros v Hf. inversion Hf.
         apply f_iszerosucc with (v := t).
      apply H.
      apply f_value. right. apply n_succ. apply H.
    intros v Hf. inversion Hf.
      subst. destruct H as [ Hb | Hn ].
        inversion Hb.
        inversion Hn.
      subst. apply f_iszerozero. apply IHHe. apply H0.
      subst. apply f_iszerosucc with (v := v0).
        apply H0.
        apply IHHe. apply H1.
Qed.

Lemma full_eval_complete_sol : forall t v,
  value v ->
  eval_many t v ->
  full_eval t v.
Proof.
  intros t v Hv Hm. induction Hm.
    apply f_value. apply Hv.
    apply eval_full_eval_sol with (t' := t').
      apply H.
      apply IHHm. apply Hv.
Qed.

Lemma pred_not_circular_sol : forall t,
  t <> tm_pred t.
Proof.
  intros t H. induction t; inversion H; auto.
Qed.

Lemma m_succ_sol : forall t u,
  eval_many t u ->
  eval_many (tm_succ t) (tm_succ u).
Proof.
  intros t u Hm.
   induction Hm; eauto using m_refl, m_step, e_succ.
Qed.

Lemma m_pred_sol : forall t u,
  eval_many t u ->
  eval_many (tm_pred t) (tm_pred u).
Proof.
  intros t u Hm.
   induction Hm; eauto using m_refl, m_step, e_pred.
Qed.

Fixpoint interp (t : tm) {struct t} : tm :=
  match t with
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 =>
      match interp t1 with
      | tm_true => interp t2
      | tm_false => interp t3
      | t4 => tm_if t4 t2 t3
      end
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (interp t1)
  | tm_pred t1 =>
      match interp t1 with
      | tm_zero => tm_zero
      | tm_succ t2 =>
          match tm_to_nat t2 with
          | some_nat _ => t2
          | no_nat => tm_pred (tm_succ t2)
          end
      | t2 => tm_pred t2
      end
  | tm_iszero t1 =>
      match interp t1 with
      | tm_zero => tm_true
      | tm_succ t2 =>
          match tm_to_nat t2 with
          | some_nat _ => tm_false
          | no_nat => tm_iszero (tm_succ t2)
          end
      | t2 => tm_iszero t2
      end
  end.

Lemma tm_to_bool_dom_includes_bvalue_sol : forall bv,
  bvalue bv -> exists b, tm_to_bool bv = some_bool b.
Proof.
  intros bv H. destruct H.
    exists true. reflexivity.
    exists false. reflexivity.
Qed.

Lemma tm_to_bool_dom_only_bvalue_sol : forall bv b,
  tm_to_bool bv = some_bool b -> bvalue bv.
Proof.
  intros bv b Heq. destruct bv.
    apply b_true.
    apply b_false.
    inversion Heq.
    inversion Heq.
    inversion Heq.
    inversion Heq.
    inversion Heq.
Qed.

Lemma tm_to_nat_dom_includes_nvalue_sol : forall v,
  nvalue v -> exists n, tm_to_nat v = some_nat n.
Proof.
  intros v Hnv. induction Hnv.
    exists O. reflexivity.
    destruct IHHnv as [ n Heq ]. exists (S n).
     simpl. rewrite -> Heq. reflexivity.
Qed.

Lemma tm_to_nat_dom_only_nvalue_sol : forall v n,
  tm_to_nat v = some_nat n -> nvalue v.
Proof.
  intros v. induction v; intros n Heq.
    inversion Heq.
    inversion Heq.
    inversion Heq.
    apply n_zero.
    apply n_succ.
     simpl in Heq. destruct (tm_to_nat v).
      inversion Heq. eapply IHv. reflexivity.
      inversion Heq.
    inversion Heq.
    inversion Heq.
Qed.

Lemma interp_reduces_sol : forall t,
  eval_many t (interp t).
Proof.
  intros t. induction t.
    apply m_refl.
    apply m_refl.
    simpl. destruct (interp t1).
      eapply m_trans.
        apply m_if. apply IHt1.
        eapply m_trans.
          eapply m_one. apply e_iftrue.
          apply IHt2.
      eapply m_trans.
        apply m_if. apply IHt1.
        eapply m_trans.
          eapply m_one. apply e_iffalse.
          apply IHt3.
      apply m_if. apply IHt1.
      apply m_if. apply IHt1.
      apply m_if. apply IHt1.
      apply m_if. apply IHt1.
      apply m_if. apply IHt1.
    apply m_refl.
    simpl. apply m_succ. apply IHt.
    simpl. destruct (interp t).
      apply m_pred. apply IHt.
      apply m_pred. apply IHt.
      apply m_pred. apply IHt.
      eapply m_trans.
        apply m_pred. apply IHt.
        apply m_one. apply e_predzero.
      remember (tm_to_nat t0) as x. destruct x.
        eapply m_trans.
          apply m_pred. apply IHt.
          apply m_one. apply e_predsucc.
           eapply tm_to_nat_dom_only_nvalue.
           rewrite <- Heqx. reflexivity.
        apply m_pred. apply IHt.
      apply m_pred. apply IHt.
      apply m_pred. apply IHt.
    simpl. destruct (interp t).
      apply m_iszero. apply IHt.
      apply m_iszero. apply IHt.
      apply m_iszero. apply IHt.
      eapply m_trans.
        apply m_iszero. apply IHt.
        apply m_one. apply e_iszerozero.
      remember (tm_to_nat t0) as x. destruct x.
        eapply m_trans.
          apply m_iszero. apply IHt.
          apply m_one. apply e_iszerosucc.
            eapply tm_to_nat_dom_only_nvalue.
            rewrite <- Heqx. reflexivity.
        apply m_iszero. apply IHt.
      apply m_iszero. apply IHt.
      apply m_iszero. apply IHt.
Qed.

Lemma interp_fully_reduces_sol : forall t,
  normal_form (interp t).
Proof.
  induction t; intros [t' H].
    inversion H.
    inversion H.
    simpl in H. destruct (interp t1).
      destruct IHt2. eauto.
      destruct IHt3. eauto.
      destruct IHt1. inversion H. eauto.
      destruct IHt1. inversion H. eauto.
      destruct IHt1. inversion H. eauto.
      destruct IHt1. inversion H. eauto.
      destruct IHt1. inversion H. eauto.
    inversion H.
    destruct IHt. inversion H. eauto.
    simpl in H. destruct (interp t).
      inversion H. inversion H1.
      inversion H. inversion H1.
      inversion H. destruct IHt. eauto.
      inversion H.
      remember (tm_to_nat t0) as x. destruct x.
        destruct IHt. exists (tm_succ t').
         apply e_succ. apply H.
        inversion H; subst.
          destruct (tm_to_nat_dom_includes_nvalue t')
           as [n Heq].
            apply H1.
            rewrite <- Heqx in Heq. inversion Heq.
          destruct IHt. eauto.
      inversion H. destruct IHt. eauto.
      inversion H. destruct IHt. eauto.
    simpl in H. destruct (interp t).
      inversion H. inversion H1.
      inversion H. inversion H1.
      inversion H. destruct IHt. eauto.
      inversion H.
      remember (tm_to_nat t0) as x. destruct x.
        inversion H.
        inversion H; subst.
          destruct (tm_to_nat_dom_includes_nvalue t0)
           as [n Heq].
            apply H1.
            rewrite <- Heqx in Heq. inversion Heq.
          inversion H. destruct IHt. eauto.
      inversion H. destruct IHt. eauto.
      inversion H. destruct IHt. eauto.
Qed.
```
