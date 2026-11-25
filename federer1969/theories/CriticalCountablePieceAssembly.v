(** Federer (1969), 3.4.2(7), p. 314: enumerate the compact
    covers of a countable family of cutting manifolds. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals topology.
From Federer Require Import GrassmannSubspaces GrassmannAbbreviations RealNormUP
  CountableDefaultEnumeration CriticalManifoldFamilyUP CriticalFlatPiecesUP
  CriticalEmptyFlatPiece CriticalFlatCoverAssembly.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [critical_countable_flat_piece_assembly]: the two
    countable indices at the end of 3.4.2(7), p. 314. Enumerate
    the cutting family, attach its proved compact covers, and
    flatten the resulting double sequence. Empty enumeration gaps
    use the proved empty compact piece on the original manifold. *)
Theorem critical_countable_flat_piece_assembly (R:realType) m d
    (Z:G (R_n R m) d) mu (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (S C A:set (R_n R m)) k (D:set (set (R_n R m))):
  critical_manifold_family Z mu 1 S ->countable D ->
  A=\bigcup_(V in D) (V `&` C) ->
  (forall V,D V ->exists T G:nat->set (R_n R m),
    (forall j,is_critical_flat_piece hNY Z mu S C k (T j) (G j)) /\
    V `&` C=\bigcup_j G j) ->
  exists T G:nat->set (R_n R m),
    (forall j,is_critical_flat_piece hNY Z mu S C k (T j) (G j)) /\A=\bigcup_j G j.
Proof.
move=>hFamily hCount hUnion hCovers.
have [u [hEnumerated hOnto]]:=countable_default_enumeration set0 hCount.
have hRows i:exists row:((nat->set (R_n R m))*(nat->set (R_n R m)))%type,
    (forall j,is_critical_flat_piece hNY Z mu S C k (row.1 j) (row.2 j)) /\
    u i `&` C=\bigcup_j row.2 j.
  case:(pselect (D (u i)))=>[hMember|hAbsent].
  - have [T [G hCover]]:=hCovers (u i) hMember.
    by exists (T,G).
  - have hEmpty:u i=set0.
      case:(hEnumerated i)=>[hBad|hEq];[exact:False_ind _ (hAbsent hBad)|exact:hEq].
    exists ((fun _=>S),(fun _=>set0));split.
    + move=>j;exact:(@critical_empty_flat_piece R m d Z mu Y NY hNY S C k hFamily).
    + rewrite hEmpty;apply/seteqP;split;[by move=>x [[] _]|by move=>x [j _ []]].
have [row hRow]:=choice hRows.
have hDouble:A=\bigcup_i \bigcup_j (row i).2 j.
  apply/seteqP;split.
  - move=>x hx;rewrite hUnion in hx;have [V hV hxV]:=hx.
    have [i hi]:=hOnto V hV.
    have hRowMember:(u i `&` C) x by rewrite hi.
    exists i;first exact:I.
    by rewrite -(hRow i).2.
  - move=>x [i _ [j _ hj]].
    have hRowMember:(u i `&` C) x.
      rewrite (hRow i).2;by exists j.
    case:(hEnumerated i)=>[hMember|hEmpty].
    + rewrite hUnion;by exists (u i).
    + by rewrite hEmpty in hRowMember;case:hRowMember=>[].
exact:(@critical_double_flat_cover R m d Z mu Y NY hNY S C A k
  (fun i=>(row i).1) (fun i=>(row i).2) (fun i j=>(hRow i).1 j) hDouble).
Qed.
