(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Instruction selection for division and modulus *)

Require Import Coqlib.
Require Import Compopts.
Require Import AST Integers Floats.
Require Import Op CminorSel SelectOp SplitLong SelectLong.

Local Open Scope cminorsel_scope.

Definition is_intconst (e: expr) : option int :=
  match e with
  | Eop (Ointconst n) _ => Some n
  | _ => None
  end.

(** We try to turn divisions by a constant into a multiplication by
  a pseudo-inverse of the divisor.  The approach is described in
- Torbjörn Granlund, Peter L. Montgomery: "Division by Invariant
  Integers using Multiplication". PLDI 1994.
- Henry S. Warren, Jr: "Hacker's Delight". Addison-Wesley.  Chapter 10.
*)

Fixpoint find_div_mul_params (fuel: nat) (nc: Z) (d: Z) (p: Z) : option (Z * Z) :=
  match fuel with
  | O => None
  | S fuel' =>
      let twp := two_p p in
      if zlt (nc * (d - twp mod d)) twp
      then Some(p, (twp + d - twp mod d) / d)
      else find_div_mul_params fuel' nc d (p + 1)
  end.

Definition divs_mul_params (d: Z) : option (Z * Z) :=
  match find_div_mul_params
          Int.wordsize
          (Int.half_modulus - Int.half_modulus mod d - 1)
          d 32 with
  | None => None
  | Some(p, m) =>
      let p := p - 32 in
      if zlt 0 d
      && zlt (two_p (32 + p)) (m * d)
      && zle (m * d) (two_p (32 + p) + two_p (p + 1))
      && zle 0 m && zlt m Int.modulus
      && zle 0 p && zlt p 32
      then Some(p, m) else None
  end.

Definition divu_mul_params (d: Z) : option (Z * Z) :=
  match find_div_mul_params
          Int.wordsize
          (Int.modulus - Int.modulus mod d - 1)
          d 32 with
  | None => None
  | Some(p, m) =>
      let p := p - 32 in
      if zlt 0 d
      && zle (two_p (32 + p)) (m * d)
      && zle (m * d) (two_p (32 + p) + two_p p)
      && zle 0 m && zlt m Int.modulus
      && zle 0 p && zlt p 32
      then Some(p, m) else None
  end.

Definition divls_mul_params (d: Z) : option (Z * Z) :=
  match find_div_mul_params
          Int64.wordsize
          (Int64.half_modulus - Int64.half_modulus mod d - 1)
          d 64 with
  | None => None
  | Some(p, m) =>
      let p := p - 64 in
      if zlt 0 d
      && zlt (two_p (64 + p)) (m * d)
      && zle (m * d) (two_p (64 + p) + two_p (p + 1))
      && zle 0 m && zlt m Int64.modulus
      && zle 0 p && zlt p 64
      then Some(p, m) else None
  end.

Definition divlu_mul_params (d: Z) : option (Z * Z) :=
  match find_div_mul_params
          Int64.wordsize
          (Int64.modulus - Int64.modulus mod d - 1)
          d 64 with
  | None => None
  | Some(p, m) =>
      let p := p - 64 in
      if zlt 0 d
      && zle (two_p (64 + p)) (m * d)
      && zle (m * d) (two_p (64 + p) + two_p p)
      && zle 0 m && zlt m Int64.modulus
      && zle 0 p && zlt p 64
      then Some(p, m) else None
  end.

Definition divu_mul (p: Z) (m: Z) :=
  shruimm (mulhu (Eletvar O) (Eop (Ointconst (Int.repr m)) Enil))
          (Int.repr p).

Definition divuimm (e1: expr) (n2: int) :=
  match Int.is_power2 n2 with
  | Some l => shruimm e1 l
  | None =>
      if optim_for_size tt then
        divu_base e1 (Eop (Ointconst n2) Enil)
      else
        match divu_mul_params (Int.unsigned n2) with
        | None => divu_base e1 (Eop (Ointconst n2) Enil)
        | Some(p, m) => Elet e1 (divu_mul p m)
        end
  end.

Definition divu (e1: expr) (e2: expr) :=
  match is_intconst e2, is_intconst e1 with
  | Some n2, Some n1 =>
      if Int.eq n2 Int.zero
      then divu_base e1 e2
      else Eop (Ointconst (Int.divu n1 n2)) Enil
  | Some n2, _ => divuimm e1 n2
  | _, _ => divu_base e1 e2
  end.

Definition mod_from_div (equo: expr) (n: int) :=
  Eop Osub (Eletvar O ::: mulimm n equo ::: Enil).

Definition moduimm (e1: expr) (n2: int) :=
  match Int.is_power2 n2 with
  | Some l => andimm (Int.sub n2 Int.one) e1
  | None =>
      if optim_for_size tt then
        modu_base e1 (Eop (Ointconst n2) Enil)
      else
        match divu_mul_params (Int.unsigned n2) with
        | None => modu_base e1 (Eop (Ointconst n2) Enil)
        | Some(p, m) => Elet e1 (mod_from_div (divu_mul p m) n2)
        end
  end.

Definition modu (e1: expr) (e2: expr) :=
  match is_intconst e2, is_intconst e1 with
  | Some n2, Some n1 =>
      if Int.eq n2 Int.zero
      then modu_base e1 e2
      else Eop (Ointconst (Int.modu n1 n2)) Enil
  | Some n2, _ => moduimm e1 n2
  | _, _ => modu_base e1 e2
  end.

Definition divs_mul (p: Z) (m: Z) :=
  let e2 :=
    mulhs (Eletvar O) (Eop (Ointconst (Int.repr m)) Enil) in
  let e3 :=
    if zlt m Int.half_modulus then e2 else add e2 (Eletvar O) in
  add (shrimm e3 (Int.repr p))
      (shruimm (Eletvar O) (Int.repr (Int.zwordsize - 1))).

Definition divsimm (e1: expr) (n2: int) :=
  match Int.is_power2 n2 with
  | Some l =>
      if Int.ltu l (Int.repr 31)
      then shrximm e1 l
      else divs_base e1 (Eop (Ointconst n2) Enil)
  | None =>
      if optim_for_size tt then
        divs_base e1 (Eop (Ointconst n2) Enil)
      else
        match divs_mul_params (Int.signed n2) with
        | None => divs_base e1 (Eop (Ointconst n2) Enil)
        | Some(p, m) => Elet e1 (divs_mul p m)
        end
  end.

Definition divs (e1: expr) (e2: expr) :=
  match is_intconst e2, is_intconst e1 with
  | Some n2, Some n1 =>
      if Int.eq n2 Int.zero
      then divs_base e1 e2
      else Eop (Ointconst (Int.divs n1 n2)) Enil
  | Some n2, _ => divsimm e1 n2
  | _, _ => divs_base e1 e2
  end.

Definition modsimm (e1: expr) (n2: int) :=
  match Int.is_power2 n2 with
  | Some l =>
      if Int.ltu l (Int.repr 31)
      then Elet e1 (mod_from_div (shrximm (Eletvar O) l) n2)
      else mods_base e1 (Eop (Ointconst n2) Enil)
  | None =>
      if optim_for_size tt then
        mods_base e1 (Eop (Ointconst n2) Enil)
      else
        match divs_mul_params (Int.signed n2) with
        | None => mods_base e1 (Eop (Ointconst n2) Enil)
        | Some(p, m) => Elet e1 (mod_from_div (divs_mul p m) n2)
        end
  end.

Definition mods (e1: expr) (e2: expr) :=
  match is_intconst e2, is_intconst e1 with
  | Some n2, Some n1 =>
      if Int.eq n2 Int.zero
      then mods_base e1 e2
      else Eop (Ointconst (Int.mods n1 n2)) Enil
  | Some n2, _ => modsimm e1 n2
  | _, _ => mods_base e1 e2
  end.

(** 64-bit integer divisions *)

Section SELECT.

Context {hf: helper_functions}.

Definition modl_from_divl (equo: expr) (n: int64) :=
  subl (Eletvar O) (mullimm n equo).

Definition divlu_mull (p: Z) (m: Z) :=
  shrluimm (mullhu (Eletvar O) (Int64.repr m)) (Int.repr p).

Definition divlu (e1 e2: expr) :=
  match is_longconst e2, is_longconst e1 with
  | Some n2, Some n1 => longconst (Int64.divu n1 n2)
  | Some n2, _ =>
      match Int64.is_power2' n2 with
      | Some l => shrluimm e1 l
      | None   => if optim_for_size tt then
                    divlu_base e1 e2
                  else
                    match divlu_mul_params (Int64.unsigned n2) with
                    | None => divlu_base e1 e2
                    | Some(p, m) => Elet e1 (divlu_mull p m)
                    end
      end
  | _, _ => divlu_base e1 e2
  end.

Definition modlu (e1 e2: expr) :=
  match is_longconst e2, is_longconst e1 with
  | Some n2, Some n1 => longconst (Int64.modu n1 n2)
  | Some n2, _ =>
      match Int64.is_power2 n2 with
      | Some l => andl e1 (longconst (Int64.sub n2 Int64.one))
      | None   => if optim_for_size tt then
                    modlu_base e1 e2
                  else
                    match divlu_mul_params (Int64.unsigned n2) with
                    | None => modlu_base e1 e2
                    | Some(p, m) => Elet e1 (modl_from_divl (divlu_mull p m) n2)
                    end
      end
  | _, _ => modlu_base e1 e2
  end.

Definition divls_mull (p: Z) (m: Z) :=
  let e2 :=
    mullhs (Eletvar O) (Int64.repr m) in
  let e3 :=
    if zlt m Int64.half_modulus then e2 else addl e2 (Eletvar O) in
  addl (shrlimm e3 (Int.repr p))
       (shrluimm (Eletvar O) (Int.repr (Int64.zwordsize - 1))).

Definition divls (e1 e2: expr) :=
  match is_longconst e2, is_longconst e1 with
  | Some n2, Some n1 => longconst (Int64.divs n1 n2)
  | Some n2, _ =>
      match Int64.is_power2' n2 with
      | Some l => if Int.ltu l (Int.repr 63)
                  then shrxlimm e1 l
                  else divls_base e1 e2
      | None   => if optim_for_size tt then
                    divls_base e1 e2
                  else
                    match divls_mul_params (Int64.signed n2) with
                    | None => divls_base e1 e2
                    | Some(p, m) => Elet e1 (divls_mull p m)
                    end
      end
  | _, _ => divls_base e1 e2
  end.

Definition modls (e1 e2: expr) :=
  match is_longconst e2, is_longconst e1 with
  | Some n2, Some n1 => longconst (Int64.mods n1 n2)
  | Some n2, _ =>
      match Int64.is_power2' n2 with
      | Some l => if Int.ltu l (Int.repr 63)
                  then Elet e1 (modl_from_divl (shrxlimm (Eletvar O) l) n2)
                  else modls_base e1 e2
      | None   => if optim_for_size tt then
                    modls_base e1 e2
                  else
                    match divls_mul_params (Int64.signed n2) with
                    | None => modls_base e1 e2
                    | Some(p, m) => Elet e1 (modl_from_divl (divls_mull p m) n2)
                    end
      end
  | _, _ => modls_base e1 e2
  end.

End SELECT.

(** Floating-point division by a constant can also be turned into a FP
    multiplication by the inverse constant, but only for powers of 2. *)

Definition divfimm (e: expr) (n: float) :=
  match Float.exact_inverse n with
  | Some n' => Eop Omulf (e ::: Eop (Ofloatconst n') Enil ::: Enil)
  | None    => Eop Odivf (e ::: Eop (Ofloatconst n) Enil ::: Enil)
  end.

(** Original definition:
<<
Nondetfunction divf (e1: expr) (e2: expr) :=
  match e2 with
  | Eop (Ofloatconst n2) Enil => divfimm e1 n2
  | _ => Eop Odivf (e1 ::: e2 ::: Enil)
  end.
>>
*)

Inductive divf_cases: forall (e2: expr), Type :=
  | divf_case1: forall n2, divf_cases (Eop (Ofloatconst n2) Enil)
  | divf_default: forall (e2: expr), divf_cases e2.

Definition divf_match (e2: expr) :=
  match e2 as zz1 return divf_cases zz1 with
  | Eop (Ofloatconst n2) Enil => divf_case1 n2
  | e2 => divf_default e2
  end.

Definition divf (e1: expr) (e2: expr) :=
  match divf_match e2 with
  | divf_case1 n2 => (* Eop (Ofloatconst n2) Enil *) 
      divfimm e1 n2
  | divf_default e2 =>
      Eop Odivf (e1 ::: e2 ::: Enil)
  end.


Definition divfsimm (e: expr) (n: float32) :=
  match Float32.exact_inverse n with
  | Some n' => Eop Omulfs (e ::: Eop (Osingleconst n') Enil ::: Enil)
  | None    => Eop Odivfs (e ::: Eop (Osingleconst n) Enil ::: Enil)
  end.

(** Original definition:
<<
Nondetfunction divfs (e1: expr) (e2: expr) :=
  match e2 with
  | Eop (Osingleconst n2) Enil => divfsimm e1 n2
  | _ => Eop Odivfs (e1 ::: e2 ::: Enil)
  end.
>>
*)

Inductive divfs_cases: forall (e2: expr), Type :=
  | divfs_case1: forall n2, divfs_cases (Eop (Osingleconst n2) Enil)
  | divfs_default: forall (e2: expr), divfs_cases e2.

Definition divfs_match (e2: expr) :=
  match e2 as zz1 return divfs_cases zz1 with
  | Eop (Osingleconst n2) Enil => divfs_case1 n2
  | e2 => divfs_default e2
  end.

Definition divfs (e1: expr) (e2: expr) :=
  match divfs_match e2 with
  | divfs_case1 n2 => (* Eop (Osingleconst n2) Enil *) 
      divfsimm e1 n2
  | divfs_default e2 =>
      Eop Odivfs (e1 ::: e2 ::: Enil)
  end.



