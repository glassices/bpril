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
    val rfvars : rthm -> term list
    
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

  let rfvars (Rhythm(asl,c,flex,rsl,_)) =
    let flex1,flex2 = unzip flex in
    freesl ((c::asl) @ flex1 @ flex2 @ rsl)

  let distill =
    let rec rev_update lst (b,a) =
      match lst with
        (b',a')::t -> if Pervasives.compare a' a = 0 then (b,a)::t
                      else (b',a')::(rev_update t (b,a))
      | [] -> [] in

    let rec convert sofar : (term * term) list =
      match sofar with
        (lst,v)::t -> if exists (fun x -> x <> None) lst then (
                        let tyl,apex = dest_fun (type_of v) in
                        let n = length tyl in
                        let bvars = map (fun i -> let name = "u" ^ (string_of_int (i+1)) in
                                                  let name = if name = (name_of v) then name ^ "'" else name in
                                                  mk_var(name,el i tyl)) (0--(n-1)) in
                        let bvars' = filter (fun (i,bvar) -> i >= (length lst) || (el i lst) = None) (zip (0--(n-1)) bvars) in
                        let args = snd (unzip bvars') in
                        let ty = mk_fun(map type_of args,apex) in
                        let tm = eta_term (mk_term bvars (mk_lcomb (mk_var(name_of v,ty)) args)) in
                        (tm,v)::(convert t)
                      ) else convert t
      | [] -> [] in

    (* can be optimized to linear *)
    let rec dup_check env tm sofar =
      match tm with
        Abs(v,bod) -> dup_check (v::env) bod sofar
      | _ -> let hs,args = strip_comb tm in
             let sofar = itlist (fun tm sofar -> dup_check env tm sofar) args sofar in
             if not (mem hs env) && not (is_const hs) && not (has_prefix (name_of hs) "mc") then (
               try let lst = rev_assoc hs sofar in
                   let n = min (length lst) (length args) in
                   let lst = map (fun i -> let a = el i lst and b = el i args in
                                           match a with
                                             Some tm -> let fvars = frees b in
                                                        if forall (fun x -> not (mem x fvars)) env &&
                                                           alphaorder tm b = 0 then Some tm 
                                                        else None
                                           | None -> None) (0--(n-1)) in
                   rev_update sofar (lst,hs)
               with Failure "find" ->
                 let lst = map (fun arg -> let fvars = frees arg in
                                           if exists (fun x -> mem x fvars) env then None
                                           else Some arg) args in
                 (lst,hs)::sofar
             ) else sofar in

    let rec work (asl,c,flex,rsl,invoke) =
      (* flex-flex pairs are broken and need further unification,
       * however, distillation might output multiple rthms
       *)
      (* Step I: fix broken flex-flex pairs *)
      let unfs = hol_unify (fvnamel (c::asl)) [] [] flex rsl in
      let raws = map (fun (ins,flex,rsl) ->
        List.sort_uniq alphaorder (map (beta_eta_term o (inst_term ins)) asl),
        beta_eta_term (inst_term ins c),flex,rsl,
        fun insl -> invoke (ins::insl)) unfs in
      (* Step II: remove dummy args *)
      (*
      let raws = List.concat(
        map (fun (asl,c,flex,rsl,invoke) ->
          let flex1,flex2 = unzip flex in
          let sofar = itlist (fun tm sofar -> dup_check [] tm sofar) (c::(asl @ flex1 @ flex2)) [] in
          let tmins = convert sofar in
          if tmins = [] then [(asl,c,flex,rsl,invoke)]
          else work (map (vsubst tmins) asl,
                     vsubst tmins c,
                     pmap (vsubst tmins) flex,
                     map (vsubst tmins) rsl,
                     fun insl -> invoke (([],tmins)::insl))) raws) in
      *)
      raws in

    fun (asl,c,flex,rsl,invoke) ->
      let raws = work (asl,c,flex,rsl,invoke) in
      (* Step III: fix trivial invoker *)
      let raws = map (fun (asl,c,flex,rsl,invoke) ->
        if length flex > 0 || length rsl > 0 then asl,c,flex,rsl,invoke
        else let th = invoke [] in
             if length (hyp th) > length asl then
               failwith "distill[fatal]: thm has more assumptions than rthm"
               (* TODO check th is identical to thm *)
             else asl,c,[],[],fun insl -> conv_thm beta_eta_conv (rev_itlist inst_thm insl th)) raws in
      (* check get_rthm works *)
      do_list (fun (asl,c,flex,rsl,invoke) ->
        let flex1,flex2 = unzip flex in
        let fvars = freesl ((c::asl) @ flex1 @ flex2 @ rsl) in
        let fvars = filter (fun v -> not (has_prefix (name_of v) "mc")) fvars in
        let constantize v =
          let tyl,apex = dest_fun (type_of v) in
          let bvs = List.mapi (fun i ty -> mk_var("u" ^ (string_of_int i),ty)) tyl in
          let hs = mk_var("fdq",apex) in
          mk_term bvs hs in
        let tmins = map (fun v -> (constantize v),v) fvars in
        try let _ = invoke [[],tmins] in ()
        with Failure s -> (print_endline s; failwith "distill[fatal]: can't invoke thm")
      ) raws;
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

    let ninfer (Rhythm(asl1,c1,_,_,invoke1)) (Rhythm(asl2,_,_,_,invoke2) as rth2) ((tyins,_) as ins,flex,rsl) =
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
              fun insl -> conv_thm beta_eta_conv (MK_COMB (invoke1 (ins::insl),invoke2 (ins::insl)))) in

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
    let rec cmap f l1 l2 =
      match l1 with
        h::t -> (map (f h) l2) @ (cmap f t l2)
      | [] -> [] in

    let update ins0 (ins,flex,rsl) =
      (merge_ins ins0 ins),flex,rsl in

    if length (rrsl rth2) > 0 then failwith "rmatchable[fatal]: rsl2 must be empty" else
    let rth1 = rnormalize rth1 "x" "A" and rth2 = rnormalize rth2 "y" "B" in
    let asl1,c1,flex1,rsl1 = dest_rthm rth1 and asl2,c2,flex2,_ = dest_rthm rth2 in
    (* match c1 and c2 and every asl1 into asl2 *)
    let const_ty = ftnamer rth2 and const_var = fvnamer rth2 in
    let avoid = union (fvnamer rth1) const_var in
    let ins0 = ([],map (fun v -> v,v) (rfvars rth1)) in
    let unfl = hol_unify avoid const_ty const_var ((c1,c2)::(flex1 @ flex2)) rsl1 in
    let unfl = map (update ins0) unfl in
    let augment tm1 tm2 ((ins,flex,rsl) : unifier) : unifier list =
      let tm1 = inst_term ins tm1 and tm2 = inst_term ins tm2 in
      let unfl = hol_unify avoid const_ty const_var ((tm1,tm2)::flex) rsl in
      map (update ins) unfl in
    let unfl = itlist (fun tm1 unfl -> List.concat (cmap (fun tm2 unf -> augment tm1 tm2 unf) asl2 unfl))
                      asl1 unfl in
    (* check *)
    do_list (fun (ins,_,_) ->
      try let _ = get_rthm rth1 [ins] in ()
      with Failure s -> (print_endline s; failwith "rmatchable[fatal]: cant get_rthm from unfl")
    ) unfl;
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

