needs "bpril/unification.ml";;

type instor =
  (hol_type * hol_type) list * (term * term) list;;

let inst_term (tyins,tmins) tm =
  vsubst tmins (inst tyins tm);;

let inst_thm (tyins,tmins) th =
  INST tmins (INST_TYPE tyins th);;

module type Rthm_kernel =
  sig
    type rthm

    val mk_rthm : thm -> rthm
    val get_rthm : rthm -> instor list -> thm
    val dest_rthm : rthm -> term list * term * (term * term) list * term list
    val rhyp : rthm -> term list
    val rconcl : rthm -> term
    val rflex : rthm -> (term * term) list
    val rrsl : rthm -> term list
    val ftnamer : rthm -> string list
    val fvnamer : rthm -> string list
    
    val rinst : instor -> rthm -> rthm list
    val rnormalize : rthm -> string -> string -> rthm
    val rtrans : rthm -> rthm -> rthm list
    val req_mp : rthm -> rthm -> rthm list
    val rmk_comb : rthm -> rthm -> rthm list
    val rdeduct : rthm -> rthm -> rthm list

    val rmatchable : rthm -> rthm -> bool

end;;

module Rthm : Rthm_kernel = struct

  type rthm = Rhythm of (term list * term * (term * term) list * term list * (instor list -> thm))

  let rec is_mogical tm =
    match tm with
      Comb(f,x) -> is_mogical f || is_mogical x
    | Abs(_,bod) -> is_mogical bod
    | Var(cname,_) -> has_prefix cname "mc"
    | Const(_,_) -> false

  let rec variant avoid name =
    if not (mem name avoid) then name
    else variant avoid (name ^ "'")

  let mk_rthm th =
    let th = conv_thm beta_eta_conv th in
    let asl,c = dest_thm th in
    let fvars = freesl (c::asl) in
    let rec work avoid tmins fvars =
      match fvars with
        h::t -> let name = fst (dest_var h) in
                let name' = variant avoid name in
                if name = name' then work (name'::avoid) tmins t
                else work (name'::avoid) ((mk_var(name',type_of h),h)::tmins) t
      | [] -> tmins in
    let tmins = work [] [] fvars in
    let th = INST tmins th in
    let asl,c = dest_thm th in
    Rhythm(asl,c,[],[],fun insl -> conv_thm beta_eta_conv (rev_itlist inst_thm insl th))

  let get_rthm (Rhythm(_,_,flex,rsl,invoke)) insl =
    if exists (fun (tm1,tm2) -> alphaorder
      (beta_eta_term (rev_itlist inst_term insl tm1))
      (beta_eta_term (rev_itlist inst_term insl tm2)) <> 0) flex then failwith "get_rthm: can't unify flex-flex pairs"
    else if exists (fun tm -> is_mogical (beta_eta_term (rev_itlist inst_term insl tm))) rsl then
      failwith "get_rthm: can't remove restricted terms"
    else invoke insl

  let dest_rthm (Rhythm(asl,c,flex,rsl,_)) = asl,c,flex,rsl
  
  let rhyp (Rhythm(asl,_,_,_,_)) = asl

  let rconcl (Rhythm(_,c,_,_,_)) = c

  let rflex (Rhythm(_,_,flex,_,_)) = flex

  let rrsl (Rhythm(_,_,_,rsl,_)) = rsl

  (* Inference steps start from here *)

  let ftnamel tml =
    let ftys = itlist (union o type_vars_in_term) tml [] in
    List.sort_uniq Pervasives.compare (map (fun x -> dest_vartype x) ftys)

  let fvnamel tml =
    List.sort_uniq Pervasives.compare (map (fun x -> name_of x) (freesl tml))

  let ftnamer (Rhythm(asl,c,flex,rsl,_)) =
    let flex1,flex2 = unzip flex in
    ftnamel ((c::asl) @ flex1 @ flex2 @ rsl)

  let fvnamer (Rhythm(asl,c,flex,rsl,_)) =
    let flex1,flex2 = unzip flex in
    fvnamel ((c::asl) @ flex1 @ flex2 @ rsl)

  let distill (asl,c,flex,rsl,invoke) =
    (* flex-flex pairs are broken and need further unification,
     * however, distillation might output multiple rthms
     *)
    (* Step I: fix broken flex-flex pairs *)
    let unfs = hol_unify (fvnamel (c::asl)) [] [] flex rsl in
    let raws = map (fun (ins,flex,rsl) ->
      List.sort_uniq alphaorder (map (beta_eta_term o (inst_term ins)) asl),
      beta_eta_term (inst_term ins c),flex,rsl,
      fun insl -> invoke (ins::insl)) unfs in
    (* Step II: fix trivial invoker *)
    let raws = map (fun (asl,c,flex,rsl,invoke) ->
      if length flex > 0 || length rsl > 0 then asl,c,flex,rsl,invoke
      else let th = invoke [] in
           if length (hyp th) > length asl then
             failwith "distill[fatal]: thm has more assumptions than rthm"
             (* TODO check th is identical to thm *)
           else asl,c,[],[],fun insl -> conv_thm beta_eta_conv (rev_itlist inst_thm insl th)) raws in
    map (fun (asl,c,flex,rsl,invoke) -> Rhythm(asl,c,flex,rsl,invoke)) raws

  let rinst ins (Rhythm(asl,c,flex,rsl,invoke)) =
    distill(map (inst_term ins) asl,
            inst_term ins c,
            pmap (inst_term ins) flex,
            map (inst_term ins) rsl,
            fun insl -> invoke (ins::insl))

  let rnormalize rth vpre tpre =
    let asl,c,flex,rsl = dest_rthm rth in
    let flex1,flex2 = unzip flex in
    let ftys = itlist (union o type_vars_in_term) ((c::asl) @ flex1 @ flex2 @ rsl) [] in
    let tyins = List.mapi (fun i fty -> (mk_vartype(tpre ^ (string_of_int (i+1))),fty)) ftys in
    let fvars = map (inst tyins) (freesl ((c::asl) @ flex1 @ flex2 @ rsl)) in
    let tmins = List.mapi (fun i fvar -> if has_prefix (fst (dest_var fvar)) "mc" then
                                           mk_var("mc" ^ vpre ^ (string_of_int (i+1)),type_of fvar),fvar
                                         else mk_var(vpre ^ (string_of_int (i+1)),type_of fvar),fvar) fvars in
    let rths = rinst (tyins,tmins) rth in
    (* Although rinst might produce multiple rthms, variable renaming won't affect flex-flex pairs *)
    if length rths <> 1 then failwith "rnormalize[fatal]: rinst return zero or multiple rthms"
    else hd rths

  (*
   * Generalized TRANS
   *)
  let rtrans rth1 rth2 =
    let infer (Rhythm(asl1,c1,_,_,invoke1)) (Rhythm(asl2,c2,_,_,invoke2)) (ins,flex,rsl) =
      let c1 = beta_eta_term (inst_term ins c1) and c2 = beta_eta_term (inst_term ins c2) in
      distill(map (inst_term ins) (asl1 @ asl2),
              mk_eq(lhs c1,rhs c2),flex,rsl,
              fun insl -> TRANS (invoke1 (ins::insl)) (invoke2 (ins::insl))) in

    let rinfer (Rhythm(asl1,c1,_,_,invoke1)) (Rhythm(asl2,c2,_,_,invoke2)) ((tyins,_) as ins,flex,rsl) =
      let c1 = beta_eta_term (inst_term ins c1) and c2 = beta_eta_term (inst_term ins c2) in
      let mvar = mk_var("mc",type_subst tyins `:C`) in
      distill(map (inst_term ins) (asl1 @ asl2),
              mk_eq(lhs c1,mk_abs(mvar,rhs c2)),flex,rsl,
              fun insl -> TRANS (invoke1 (ins::insl)) 
                                (conv_concl eta_conv
                                            (ABS (rev_itlist (fun ins v -> inst_term ins v) insl mvar)
                                                 (invoke2 (ins::insl))))) in

    let linfer (Rhythm(asl1,c1,_,_,invoke1)) (Rhythm(asl2,c2,_,_,invoke2)) ((tyins,_) as ins,flex,rsl) =
      let c1 = beta_eta_term (inst_term ins c1) and c2 = beta_eta_term (inst_term ins c2) in
      let mvar = mk_var("mc",type_subst tyins `:C`) in
      distill(map (inst_term ins) (asl1 @ asl2),
              mk_eq(mk_abs(mvar,lhs c1),rhs c2),flex,rsl,
              fun insl -> TRANS (conv_concl eta_conv
                                            (ABS (rev_itlist (fun ins v -> inst_term ins v) insl mvar)
                                                 (invoke1 (ins::insl))))
                                (invoke2 (ins::insl))) in

    let rth1 = rnormalize rth1 "x" "A" and rth2 = rnormalize rth2 "y" "B" in
    let avoid = union (fvnamer rth1) (fvnamer rth2) in
    (* vanilla *)
    let tm1 = mk_eq(`u:C`,`v:C`) and tm2 = mk_eq(`v:C`,`w:C`) in
    let unfs = hol_unify avoid [] []
      ((rconcl rth1,tm1)::(rconcl rth2,tm2)::((rflex rth1) @ (rflex rth2)))
      ((rrsl rth1) @ (rrsl rth2)) in
    let ans = List.concat (map (fun unf -> infer rth1 rth2 unf) unfs) in
    let tm = mk_eq(`p:C->D`,`q:C->D`) and tm' = mk_eq(`u:D`,`v:D`) in
    let unfs = hol_unify avoid [] []
      ((rconcl rth1,tm)::(rconcl rth2,tm')::(mk_comb(`q:C->D`,mk_var("mc",`:C`)),`u:D`)::((rflex rth1) @ (rflex rth2)))
      ((rconcl rth1)::((rrsl rth1) @ (rrsl rth2) @ (rhyp rth1) @ (rhyp rth2))) in
    let ansr = List.concat (map (fun unf -> rinfer rth1 rth2 unf) unfs) in
    let unfs = hol_unify avoid [] []
      ((rconcl rth1,tm')::(rconcl rth2,tm)::(mk_comb(`p:C->D`,mk_var("mc",`:C`)),`v:D`)::((rflex rth1) @ (rflex rth2)))
      ((rconcl rth2)::((rrsl rth1) @ (rrsl rth2) @ (rhyp rth1) @ (rhyp rth2))) in
    let ansl = List.concat (map (fun unf -> linfer rth1 rth2 unf) unfs) in
    ans @ ansr @ ansl

  (*
   * Generalized EQ_MP
   *)
  let req_mp rth1 rth2 =
    let infer (Rhythm(asl1,c1,_,_,invoke1)) (Rhythm(asl2,_,_,_,invoke2)) (ins,flex,rsl) =
      let c1 = beta_eta_term (inst_term ins c1) in
      distill(map (inst_term ins) (asl1 @ asl2),
              rhs c1,flex,rsl,
              fun insl -> EQ_MP (invoke1 (ins::insl)) (invoke2 (ins::insl))) in

    let ninfer (Rhythm(asl1,c1,_,_,invoke1)) (Rhythm(asl2,_,_,_,invoke2)) ((tyins,_) as ins,flex,rsl) =
      let c1 = beta_eta_term (inst_term ins c1) in
      let mvar = mk_var("mc",type_subst tyins `:C`) in
      distill(map (inst_term ins) (asl1 @ asl2),
              rhs c1,flex,rsl,
              fun insl -> EQ_MP (invoke1 (ins::insl))
                                (conv_concl eta_conv
                                            (ABS (rev_itlist (fun ins v -> inst_term ins v) insl mvar)
                                                 (invoke2 (ins::insl))))) in

    let rth1 = rnormalize rth1 "x" "A" and rth2 = rnormalize rth2 "y" "B" in
    let tm1 = mk_eq(`u:bool`,`v:bool`) and tm2 = `u:bool` in
    let avoid = union (fvnamer rth1) (fvnamer rth2) in
    let unfs = hol_unify avoid [] []
      ((rconcl rth1,tm1)::(rconcl rth2,tm2)::((rflex rth1) @ (rflex rth2)))
      ((rrsl rth1) @ (rrsl rth2)) in
    let ans = List.concat (map (fun unf -> infer rth1 rth2 unf) unfs) in
    (* abstraction *)
    let tm1 = mk_eq(mk_eq(`p:C->D`,`q:C->D`),`r:bool`) and tm2 = mk_eq(`u:D`,`v:D`) in
    let unfs = hol_unify avoid [] []
      ((rconcl rth1,tm1)::(rconcl rth2,tm2)::(mk_comb(`p:C->D`,mk_var("mc",`:C`)),`u:D`)::(mk_comb(`q:C->D`,mk_var("mc",`:C`)),`v:D`)::((rflex rth1) @ (rflex rth2)))
      ((rconcl rth1)::((rrsl rth1) @ (rrsl rth2) @ (rhyp rth1) @ (rhyp rth2))) in
    let anss = List.concat (map (fun unf -> ninfer rth1 rth2 unf) unfs) in
    ans @ anss

  (*
   * Generalized MK_COMB
   *)
  let rmk_comb rth1 rth2 =
    let infer (Rhythm(asl1,c1,_,_,invoke1)) (Rhythm(asl2,c2,_,_,invoke2)) (ins,flex,rsl) =
      let c1 = beta_eta_term (inst_term ins c1) and c2 = beta_eta_term (inst_term ins c2) in
      distill(map (inst_term ins) (asl1 @ asl2),
              mk_eq(mk_comb(lhs c1,lhs c2),mk_comb(rhs c1,rhs c2)),flex,rsl,
              fun insl -> MK_COMB (invoke1 (ins::insl),invoke2 (ins::insl))) in

    let rth1 = rnormalize rth1 "x" "A" and rth2 = rnormalize rth2 "y" "B" in
    let tm1 = mk_eq(`p:C->D`,`q:C->D`) and tm2 = mk_eq(`u:C`,`v:C`) in
    let avoid = union (fvnamer rth1) (fvnamer rth2) in
    let unfs = hol_unify avoid [] []
      ((rconcl rth1,tm1)::(rconcl rth2,tm2)::((rflex rth1) @ (rflex rth2)))
      ((rrsl rth1) @ (rrsl rth2)) in
    List.concat (map (fun unf -> infer rth1 rth2 unf) unfs)

  (*
   * Generalized DEDUCT_ANTISYM_RULE
   *)
  let rdeduct rth1 rth2 =
    let rec fetch v ls =
      match ls with
        h::t -> if (land) v 1 = 0 then h::(fetch ((lsr) v 1) t)
                else fetch ((lsr) v 1) t
      | [] -> [] in

    let infer v1 v2 (Rhythm(asl1,c1,_,_,invoke1)) (Rhythm(asl2,c2,_,_,invoke2)) (ins,flex,rsl) =
      let asl1 = fetch v1 asl1 and asl2 = fetch v2 asl2 in
      distill(map (inst_term ins) (asl1 @ asl2),
              mk_eq(inst_term ins c1,inst_term ins c2),flex,rsl,
              fun insl -> DEDUCT_ANTISYM_RULE (invoke1 (ins::insl)) (invoke2 (ins::insl))) in

    let rth1 = rnormalize rth1 "x" "A" and rth2 = rnormalize rth2 "y" "B" in
    let avoid = union (fvnamer rth1) (fvnamer rth2) in
    let asl1,c1,_,_ = dest_rthm rth1 and asl2,c2,_,_ = dest_rthm rth2 in
    let n1 = length asl1 and n2 = length asl2 in
    List.concat (map (
      fun v -> let v1 = (land) v (((lsl) 1 n1)-1) in
               let v2 = (lsr) v n1 in
               let rec f1 k =
                 if k = n1 then []
                 else if (land) ((lsr) v1 k) 1 = 0 then f1 (k+1)
                 else (el k asl1,c2)::(f1 (k+1)) in
               let rec f2 k =
                 if k = n2 then []
                 else if (land) ((lsr) v2 k) 1 = 0 then f2 (k+1)
                 else (el k asl2,c1)::(f2 (k+1)) in
               let unfs = hol_unify avoid [] [] ((f1 0) @ (f2 0) @ (rflex rth1) @ (rflex rth2)) ((rrsl rth1) @ (rrsl rth2)) in
               List.concat (map (fun (ins,flex,rsl) -> infer v1 v2 rth1 rth2 (ins,flex,rsl)) unfs))
      (1--(((lsl) 1 (n1+n2))-1)))

  (* Some utilities *)
  let rmatchable rth1 rth2 =
    if length (rrsl rth2) > 0 then failwith "rmatchable[fatal]: rsl2 must be empty" else
    let rth1 = rnormalize rth1 "x" "A" and rth2 = rnormalize rth2 "y" "B" in
    let asl1,c1,flex1,rsl1 = dest_rthm rth1 and asl2,c2,flex2,_ = dest_rthm rth2 in
    (* match c1 and c2 and every asl1 into asl2 *)
    let const_ty = ftnamer rth2 and const_var = fvnamer rth2 in
    let avoid = union (fvnamer rth1) const_var in
    let unfl = hol_unify avoid const_ty const_var ((c1,c2)::(flex1 @ flex2)) rsl1 in
    let augment tm1 tm2 ((ins,flex,rsl) : unifier) : unifier list =
      let tm1 = inst_term ins tm1 and tm2 = inst_term ins tm2 in
      hol_unify avoid const_ty const_var ((tm1,tm2)::flex) rsl in
    let unfl = itlist (fun tm1 unfl -> List.concat (map (fun tm2 -> List.concat (map (fun unf -> augment tm1 tm2 unf) unfl)) asl2))
                      asl1 unfl in
    length unfl > 0

end;;

include Rthm;;

let pp_print_rthm fmt rth =
  let ss_term tm =
    let s = string_of_term tm in
    let ls = map (fun x -> if x = "\n" then " " else x) (explode s) in
    let rec work ls =
      match ls with
        a::(b::t) -> if a = " " then
                       if b = " " then work (b::t)
                       else a::b::(work t)
                     else a::(work (b::t))
      | _ -> ls in
    String.concat "" (work ls) in

  let asl,tm,flex,rsl = dest_rthm rth in
  (if not (asl = []) then
    (if !print_all_thm then
      (pp_print_string fmt (ss_term (hd asl));
       do_list (fun x -> pp_print_string fmt ",";
                         pp_print_space fmt ();
                         pp_print_string fmt (ss_term x))
               (tl asl))
     else pp_print_string fmt "...";
     pp_print_space fmt ())
   else ();
   pp_open_hbox fmt();
   pp_print_string fmt "|- ";
   pp_print_string fmt (ss_term tm);
   if not (flex = []) then (
     pp_print_space fmt ();
     pp_print_string fmt "[";
     pp_print_string fmt (ss_term (fst (hd flex)));
     pp_print_string fmt ",";
     pp_print_string fmt (ss_term (snd (hd flex)));
     do_list (fun x -> pp_print_string fmt ";";
                       pp_print_space fmt ();
                       pp_print_string fmt (ss_term (fst x));
                       pp_print_string fmt ",";
                       pp_print_string fmt (ss_term (snd x)))
             (tl flex);
     pp_print_string fmt "]";
   ) else ();
   if not (rsl = []) then (
     pp_print_space fmt ();
     pp_print_string fmt "{";
     pp_print_string fmt (ss_term (hd rsl));
     do_list (fun x -> pp_print_string fmt ";";
                       pp_print_space fmt ();
                       pp_print_string fmt (ss_term x))
             (tl rsl);
     pp_print_string fmt "}";
   ) else ();
   pp_close_box fmt ());;

let print_rthm = pp_print_rthm std_formatter;;
#install_printer print_rthm;;

let T_TAUT = DEDUCT_ANTISYM_RULE (ASSUME `t:bool`) TRUTH;;
let refl = mk_rthm (REFL `x`);;
let assume = mk_rthm (ASSUME `x:bool`);;
let t_def = mk_rthm T_DEF;;
let and_def = mk_rthm AND_DEF;;
let t_taut = mk_rthm(T_TAUT);;
let r0 = mk_rthm(T_DEF);;
let r4 = el 0 (rmk_comb refl r0);;
let r5 = el 0 (rmk_comb r4 refl);;
let r6 = el 1 (req_mp r5 refl);;
let r7 = el 1 (req_mp r6 refl);;
let r18 = mk_rthm(AND_DEF);;
let r93 = el 0 (rmk_comb r18 refl);;
let r100 = el 0 (rmk_comb r93 refl);;
let r107 = el 0 (req_mp r100 assume);;
let r109 = el 0 (rmk_comb r107 refl);;
let r136 = el 0 (rmk_comb refl r109);;
let r137 = el 0 (rmk_comb r136 refl);;
let r138 = el 2 (req_mp r137 refl);;
let r139 = el 0 (req_mp r138 r7);;
let r4725 = el 1 (rdeduct assume r139);;
let r4726 = el 0 (req_mp r4725 assume);;
let r491 = r4725;;
let r492 = r4726;;
let r447 = r491;;
let r448 = r492;;
let r421 = mk_rthm(FORALL_DEF);;
let r424 = el 0 (rmk_comb r421 refl);;
let r425 = el 0 (req_mp r424 assume);;
let r429 = el 0 (rmk_comb r425 refl);;
let r436 = el 0 (rmk_comb refl r429);;
let r437 = el 0 (rmk_comb r436 refl);;
let r438 = el 3 (req_mp r437 refl);;
let r439 = el 0 (req_mp r438 r7);;
let r9 = mk_rthm(T_TAUT);;
let r13 = el 0 (rmk_comb refl assume);;
let r14 = el 0 (rmk_comb r13 refl);;
let r15 = el 2 (req_mp r14 refl);;
let r16 = el 0 (req_mp r15 r7);;
let r17 = el 2 (rdeduct r16 r9);;
let r66 = el 0 (req_mp r17 assume);;
let r68 = r66;;
let r70 = el 0 (rmk_comb refl r68);;
let r71 = el 0 (rmk_comb r70 r66);;
let r74 = el 0 (rmk_comb r18 refl);;
let r76 = el 0 (rmk_comb r74 refl);;
let r87 = el 0 (rmk_comb refl r76);;
let r88 = el 0 (rmk_comb r87 refl);;
let r89 = el 1 (req_mp r88 refl);;
let r90 = el 4 (req_mp r89 r71);;
let r20 = el 0 (rmk_comb r18 refl);;
let r26 = el 0 (rmk_comb r20 refl);;
let r32 = el 0 (req_mp r26 assume);;
let r34 = el 0 (rmk_comb r32 refl);;
let r59 = el 0 (rmk_comb refl r34);;
let r60 = el 0 (rmk_comb r59 refl);;
let r61 = el 2 (req_mp r60 refl);;
let r62 = el 1 (req_mp r61 r7);;
let r91 = el 4 (rdeduct r62 r90);;
let r442 = el 1 (rdeduct assume r91);;
let r443 = el 0 (req_mp r442 assume);;
let r444 = el 0 (req_mp r443 r439);;
let r449 = rdeduct r444 r448;
