From Coq Require Import 
    Sets.Ensembles
    Strings.String
    Lists.List
    Arith
    .

From ExtLib Require Import
    Data.Map.FMapAList
    Structures.Monad
    Data.Nat
    Data.String
    Core.RelDec
    .

From RecordUpdate Require Import RecordSet.

From EGraph Require Import DisjointSet.

Import ListNotations.
Import MonadNotation.
Import RecordSetNotations.
Open Scope list_scope.
Open Scope nat_scope.
Open Scope monad_scope.

Record Term := mkTerm {
    body : string ;
    args : list nat
}.

Instance RelDec_eq : RelDec (@eq Term) := { 
    rel_dec t1 t2 := String.eqb (body t1) (body t2) 
}.

Record EClass := mkEClass {
    nodes : list Term ;
    parents : alist Term nat
}. 

Record EGraph := mkEGraph {
    unionfind: DisjointSet ;
    terms: alist Term nat ;
    eclasses: alist nat EClass ;
    dirty_union: list nat ;
    dirty_id: nat
}.

#[export] Instance etaEGraph : Settable _ := settable! 
    mkEGraph <unionfind; terms; eclasses; dirty_union; dirty_id>.

#[export] Instance etaEClass : Settable _ := settable! 
    mkEClass <nodes; parents>.

Definition default_egraph : EGraph := {|
    unionfind := dset_init;
    terms := [] ;
    eclasses := [] ;
    dirty_union := [] ;
    dirty_id := 0
|}.

Definition find_root (e: EGraph) (id: nat) : nat := 
    dset_root (unionfind e) id.

Definition in_same_class (e: EGraph) (t1: Term) (t2: Term) : bool :=
    let term2id := terms e in
    let dest := unionfind e in
    let id1 := alist_find RelDec_eq t1 term2id in
    let id2 := alist_find RelDec_eq t2 term2id in
    match (id1, id2) with
    | (Some id1', Some id2') => if in_same_set dest id1' id2' then true else false
    | _ => false
    end.

Definition canonicalize (e: EGraph) (t : Term) : Term := 
    let child := args t in
    let new_args := (fix F e child := 
        match child with
        | x :: xs => (find_root e x) :: (F e xs)
        | [] => []
        end) e child in 
    {| body := body t ;
       args := new_args |}.

Definition find_class (e: EGraph) (t: Term) : option nat := 
    let new_term := canonicalize e t in
    match alist_find RelDec_eq new_term (terms e) with
    | None => None
    | Some id => Some (find_root e id)
    end.

Definition push_term (e: EGraph) (t: Term) : nat * EGraph := 
    match find_class e t with
    | Some id => (id, e)
    | None => 
        let id := dirty_id e in
        let cls := {| nodes := [t]; parents := [] |} in
        let eclasses' := (fix F eclass arg :=
            match arg with 
            | x :: xs => 
                match alist_find Nat.RelDec_eq x eclass with
                | None => F eclass xs
                | Some arg_eclass => 
                    let arg_eclass' := arg_eclass <| parents := (t, id) :: (parents arg_eclass) |> in
                    let eclass' := alist_add Nat.RelDec_eq x arg_eclass' eclass in
                    F eclass' xs
                end
            | [] => eclass
            end) (eclasses e) (args t) in
        let e' := e <| eclasses := alist_add Nat.RelDec_eq id cls eclasses' |> 
                    <| terms := alist_add RelDec_eq t id (terms e) |> in
        (id, e)
    end.

Definition _union (e: EGraph) (id1: nat) (id2: nat) : option EGraph := 
    let eclass1 := alist_find Nat.RelDec_eq id1 (eclasses e) in
    let eclass2 := alist_find Nat.RelDec_eq id2 (eclasses e) in
    match eclass1, eclass2 with
    | Some eclass1, Some eclass2 => 
        (*move every nodes in eclass2 to eclass1*)
        let eclass1' := eclass1 <| nodes := (nodes eclass1) ++ (nodes eclass2)|> in
        (*canonicalize every term again after the unionfind happen in union*)
        let e' := (fix F e nodes := 
            match nodes with
            | x :: xs => let terms' := alist_remove RelDec_eq x (terms e) in
                         let e' := e <| terms := terms' |> in
                         let x' := canonicalize e' x in
                         let e'' := e <| terms := alist_add RelDec_eq x' id1 terms' |> in
                         F e'' xs
            | [] => e
            end
        ) e (nodes eclass1') in 
        (* merge parent list of eclass1 and 2 *)
        let parents1' := (fix F parents1 parents2 :=
            match parents2 with
            | (t, id) :: xs => let parents1' := (t, find_root e' id) :: parents1 in
                               F parents1' xs
            | [] => parents1
            end
        ) (parents eclass1) (parents eclass2) in 
        let eclass1'' := eclass1' <| parents :=  parents1'|> in
        (* delete eclass2 since it lives in eclass1 now*)
        let eclasses' := alist_add Nat.RelDec_eq id1 eclass1''
                        (alist_remove Nat.RelDec_eq id2 (eclasses e')) in           
        Some (e' <| eclasses := eclasses' |>)
    | _, _ => None
    end.

Definition union (e: EGraph) (id1: nat) (id2: nat) : option EGraph := 
    let id1 := find_root e id1 in
    let id2 := find_root e id2 in
    if negb(id1 =? id2) then 
        let dset := DisjointSet.union (unionfind e) id1 id2 in
        let id3 := dset_root dset id1 in
        let e' := e <| dirty_union := id3 :: (dirty_union e)|> in
        if id3 =? id1 then
            _union e' id1 id2
        else if id3 =? id2 then
            _union e' id2 id1
        else None
    else Some e.
    
Definition repair (e: EGraph) (id: nat) : option EGraph := 
    match alist_find Nat.RelDec_eq id (eclasses e) with
    | None => None 
    | Some cls =>
        (*repair every parents for id*)
        let e' := (fix F parent e := 
            match parent with
            | (t, id) :: xs => 
                let terms' := alist_remove RelDec_eq t (terms e) in
                let e' := e <| terms := terms' |> in
                let t' := canonicalize e' t in
                let terms'' := alist_add RelDec_eq t' (find_root e' id) terms' in
                F xs (e <| terms := terms'' |>)
            | [] => e
            end
        ) (parents cls) e in
        (*search for new congruence equality*)
        let (parents', e'') := (fix F parents parents' e := 
            match parents with
            | (t, id) :: xs => 
                match alist_find RelDec_eq t parents' with
                | Some id' => 
                    match union e id id' with
                    | Some egraph => 
                        let parents'' := alist_add RelDec_eq t (find_root egraph id) parents' in
                        F xs parents'' egraph
                    | None => F xs parents' e
                    end
                | None => F xs parents' e
                end
            | [] => (parents', e)
            end) (parents cls) [] e' in
        let cls' := cls <| parents := parents' |> in 
        Some (e'' <| eclasses := alist_add Nat.RelDec_eq id cls' (eclasses e'') |>)
    end.

Definition rebuild (e: EGraph) : option EGraph :=
    (fix F dirty e := 
        match dirty with
        | x :: xs => let root := find_root e x in
                     match repair e root with
                     | None => None 
                     | Some e' => F xs e'
                     end
        | [] => Some e
        end) (dirty_union e) e.

Definition add_const (e: EGraph) (x: string) := 
    let t := {| body := x; args := [] |} in
    push_term e t.

Definition add_term (e: EGraph) (t: string) (args: list nat) := 
    let t := {| body:= t; args := args |} in
    push_term e t.