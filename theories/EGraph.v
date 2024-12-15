From Coq Require Import 
    Sets.Ensembles
    .

From ExtLib Require Import
    Data.Map.FMapAList
    .



Inductive EClass := mkEClass {
    nodes : list Term
    parents : list (Term, nat)
}.