From Coq Require Import
    Arith.

Section DisjointSet.

Definition DisjointSet := nat -> nat.
Definition dset_init : DisjointSet := fun x => x.
Definition dset_root (set : DisjointSet) x := set x.
Definition in_same_set (set : DisjointSet) x y := Nat.eq_dec (set x) (set y).

Definition union (g : DisjointSet) x y : DisjointSet :=
    let px := dset_root g x in
    let py := dset_root g y in
    if Nat.eq_dec px py then
        g
    else
        fun z => let pz := dset_root g z in
        if Nat.eq_dec px pz
            then py
            else pz.

Definition In_Same_Set f x y := exists p, in_same_set f x y = left p.

Lemma nat_eq_dec_refl : forall x, exists p, Nat.eq_dec x x = left p.
Proof.
    intros. destruct (Nat.eq_dec x x).
    - now eexists.
    - unfold "<>" in n. exfalso. now apply n.
Qed.

Theorem disjoint_refl : forall f x, In_Same_Set f x x.
Proof.
    intros. unfold In_Same_Set, in_same_set. 
    apply nat_eq_dec_refl.
Qed.

Theorem disjoint_sym : forall f x y, 
In_Same_Set f x y -> In_Same_Set f y x.
Proof.
    intros. unfold In_Same_Set, in_same_set.
    destruct H. destruct (Nat.eq_dec (f y) (f x)).
    - now eexists.
    - exfalso. apply n. now rewrite x0.
Qed.

Theorem disjoint_trans : forall f x y z,
In_Same_Set f x y -> In_Same_Set f y z -> In_Same_Set f x z.
Proof.
    intros. unfold In_Same_Set, in_same_set.
    destruct H, H0.
    destruct (Nat.eq_dec (f x) (f z)).
    - now eexists.
    - exfalso. apply n. now rewrite x0.
Qed.

Theorem disjoint_neq : forall x y, 
x <> y -> exists p, in_same_set dset_init x y = right p.
Proof.
    intros.
    unfold in_same_set. 
    unfold dset_init.
    destruct (Nat.eq_dec x y).
    - exfalso. now apply H.
    - now exists n.
Qed.

Theorem disjoint_union : forall f x y,
In_Same_Set (union f x y) x y.
Proof.
    intros. unfold In_Same_Set. 
    unfold in_same_set.
    unfold union. 
    unfold dset_root;
    destruct (Nat.eq_dec (f x) (f y));
    destruct (Nat.eq_dec (f x) (f x));
    destruct (Nat.eq_dec (f x) (f y));
    destruct (Nat.eq_dec (f y) (f y));
    try (exfalso; now auto);
    now eexists.
Qed.

End DisjointSet.