(* A port of Phil Wadler's "A Prettier Printer" library in Haskell to Coq.
   See http://homepages.inf.ed.ac.uk/wadler/papers/prettier/prettier.pdf.
*)

Require String List.
Import List.ListNotations.
Local Open Scope list_scope.

Delimit Scope string_scope with string.
Bind Scope string_scope with String.string.
Local Open Scope string_scope.

Require Import Arith Program Omega Wf_nat.

Module internal.
  (* This is what Wadler calls DOC. *)
  Inductive t : Type :=
  | nil : t
  | app : t -> t -> t
  | nest : nat -> t -> t
  | text : String.string -> t
  | line : t
  | union : t -> t -> t
  .

  (* This is needed to perform general recursion over DOCs. *)
  Fixpoint size (d : t) : nat :=
    match d with
    | nil => 1
    | app d1 d2 => S (size d1 + size d2)
    | nest _ d' => S (size d')
    | text s => 1
    | line => 1
    | union d1 d2 => S (size d1 + size d2)
    end.

  Lemma size_nonzero : forall d, 0 < size d.
  Proof. destruct d; simpl; omega. Qed.

  Local Notation "a <|> b" := (union a b) (at level 60, b at level 60).

  Fixpoint flatten (d : t) : t :=
    match d with
    | nil => nil
    | app d1 d2 => app (flatten d1) (flatten d2)
    | nest n d => nest n (flatten d)
    | text s => text s
    | line => text " "
    | union d1 d2 => flatten d1
    end.

  Lemma flatten_size_le : forall d, size (flatten d) <= size d.
  Proof. induction d; simpl; omega. Qed.
End internal.

Local Notation "a ++ b" := (String.append a b).

Module string_utils.
  Fixpoint repeat (n : nat) (s : String.string) : String.string :=
    match n with
    | 0 => ""
    | S n' => s ++ repeat n' s
    end.
End string_utils.
Import string_utils.

Module nat_utils.
  Fixpoint sum (l : list nat) : nat :=
    match l with
    | [] => 0
    | x :: xs => x + sum xs
    end.
End nat_utils.
Import nat_utils.

Module rendered.
  (* This is what Wadler calls Doc. *)
  Inductive t : Type :=
  | nil : t
  | text : String.string -> t -> t
  | line : nat -> t -> t
  .

  Fixpoint layout (d : t) : String.string :=
    match d with
    | nil => ""
    | text s d' => s ++ layout d'
    | line n d' => repeat n " " ++ layout d'
    end.

  (* introduce extra parameter k to avoid need for negative numbers in
     wadler's implementation. *)
  Fixpoint fits (w k : nat) (d : t) : bool :=
    if w <? k then false
    else
      match d with
      | nil => true
      | text s d' => fits w (k + String.length s) d'
      | line i d' => true
      end.

  Definition better (w k : nat) (x y : t) : t :=
    if fits w k x then x else y.

  Local Notation size := internal.size.

  (* Since Wadler's definition of the function `be` is not structurally recursive,
     we use well founded recursion. *)
  Module be.
    Definition A : Type := nat * list (nat * internal.t).

    Definition measure (x : A) : nat :=
      sum (List.map (fun p => size (snd p)) (snd x)).

    Definition R (x y : A) : Prop :=
      ltof _ measure x y.

    Lemma R_wf : well_founded R.
    Proof. apply well_founded_ltof. Qed.

    Definition f' (w : nat) : A -> rendered.t.
      refine (Fix R_wf _ (fun p => match p with (k, l) => _ end)). clear p.
      refine
        match l with
        | [] => fun _ => nil
        | (i, internal.nil) :: z => fun rec => rec (k, z) _
        | (i, internal.app x y) :: z => fun rec => rec (k, ((i,x) :: (i, y) :: z)) _
        | (i, internal.nest j x) :: z => fun rec => rec (k, ((i + j, x) :: z)) _
        | (i, internal.text s) :: z => fun rec => text s (rec ((k+String.length s), z) _)
        | (i, internal.line) :: z => fun rec => line i (rec (i, z) _)
        | (i, internal.union x y) :: z => fun rec =>
                                           better w k
                                                  (rec (k, ((i,x) :: z)) _)
                                                  (rec (k, ((i,y) :: z)) _)
        end; unfold R, ltof, measure; simpl; omega.
    Defined.

    Definition f (w k : nat) (l : list (nat * internal.t)) : rendered.t :=
      f' w (k, l).
  End be.

  Definition be := be.f.

  Definition best w k x := be w k [(0, x)].
End rendered.

Module pretty.
  Definition Doc := internal.t.

  Local Notation t := Doc.
  Delimit Scope pretty_scope with pretty.
  Bind Scope pretty_scope with Doc.
  Open Scope pretty_scope.


  Definition nil : t := internal.nil.
  Definition app : t -> t -> t := internal.app.
  Definition nest : nat -> t -> t := internal.nest.
  Definition text : String.string -> t := internal.text.
  Definition line : t := internal.line.

  Definition pretty (w : nat) (d : t) : String.string :=
    rendered.layout (rendered.best w 0 d).

  Notation "a ++ b" := (app a b) : pretty_scope.
  Notation "a <|> b" := (internal.union a b) (at level 60, b at level 60) : pretty_scope.

  Definition app_space x y := x ++ (text " ") ++ y.
  Notation "a <+> b" := (app_space a b) (at level 60, b at level 60) : pretty_scope.

  Definition app_line x y := x ++ line ++ y.
  Notation "a </> b" := (app_line a b) (at level 60, b at level 60) : pretty_scope.

  Definition folddoc (f : t -> t -> t) (l : list t) : t :=
    List.fold_right f nil l.

  Definition spread := folddoc app_space.
  Definition stack := folddoc app_line.

  Definition group (d : t) : t :=  internal.flatten d <|> d.

  Definition bracket l x r := group (text l ++
                                          nest 2 (line ++ x) ++
                                          line ++ text r).

  Definition app_space_or_line x y := x ++ (text " " <|> line) ++ y.
  Notation "a <+/> b" := (app_line a b) (at level 60, b at level 60) : pretty_scope.

  Module fill.
    Definition A : Type := list t.

    Definition measure (x : A) : nat :=
      sum (List.map internal.size x).

    Definition R (x y : A) : Prop :=
      ltof _ measure x y.

    Lemma R_wf : well_founded R.
    Proof. apply well_founded_ltof. Qed.

    Definition f' : A -> t.
      refine (Fix R_wf _ (fun l => _)).
      refine
        match l with
        | [] => fun _ => nil
        | [x] => fun _ => x
        | x :: y :: zs => fun rec => (internal.flatten x <+> rec (internal.flatten y :: zs) _) <|>
                                                                                           (x </> rec (y :: zs) _)
        end; clear rec; unfold R, ltof, measure; simpl.
      - pose proof internal.flatten_size_le y.
        pose proof internal.size_nonzero x.
        abstract omega.
      - pose proof internal.size_nonzero x.
        abstract omega.
    Defined.

    Definition f (l : list t) : t := f' l.
  End fill.

  Definition fill := fill.f.
End pretty.

Import pretty.

Module examples.
  Module tree.
    (* Multiarity trees such as this are not very well
      supported. We're going to have to write nested fix expressions by hand. *)
    Local Unset Elimination Schemes.
    Inductive Tree := Node : String.string -> list Tree -> Tree.

    (* Wadler's use of mutual recursion is not directly expressible in Coq.
       We first have to define the showTrees and showBracket functions *locally*,
       and then repeat the definitions in the outer scope. *)
    Definition showTree :=
      fix showTree (t : Tree) : Doc :=
          let fix showTrees (l : list Tree) : Doc :=
              match l with
              | [] => nil
              | [t] => showTree t
              | t :: ts => showTree t ++ text "," ++ line ++ showTrees ts
              end in
          let showBracket l :=
              match l with
              | [] => nil
              | _ => text "[" ++ nest 1 (showTrees l) ++ text "]"
              end in
          match t with
          | Node s l => group (text s ++ nest (String.length s) (showBracket l))
          end.

    (* copy pasta from above *)
    Definition showTrees :=
      fix showTrees (l : list Tree) : Doc :=
          match l with
          | [] => nil
          | [t] => showTree t
          | t :: ts => showTree t ++ text "," ++ line ++ showTrees ts
          end.

    (* copy pasta from above *)
    Definition showBracket l :=
      match l with
      | [] => nil
      | _ => text "[" ++ nest 1 (showTrees l) ++ text "]"
      end.

    Definition showTrees' (l : list Tree) : Doc :=
      match l with
      | [] => nil
      | [t] => showTree t
      | t :: ts => showTree t ++ text "," ++ line ++ showTrees ts
      end.

    Definition showBracket' (l : list Tree) : Doc :=
      match l with
      | [] => nil
      | _ => bracket "[" (showTrees' l) "]"
      end.

    Definition showTree' (t : Tree) : Doc :=
      match t with
      | Node s l => text s ++ showBracket' l
      end.

    Definition tree :=
      Node "aaa" [
             Node "bbbbb" [
                    Node "ccc" [];
                      Node "dd" []
                  ];
               Node "eee" [];
               Node "ffff" [
                      Node "gg" [];
                        Node "hhh" [];
                        Node "ii" []
                    ]
           ].

    Eval compute in (showTree tree).      (* looks reasonable... *)

    Definition testtree w := pretty w (showTree tree).

    (* This hangs because Coq spends all its time computing proof terms.
       It should work if you extract it to Haskell. *)
    (* Eval compute in testtree 10. *)
  End tree.
End examples.
