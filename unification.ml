needs "bpril/kit.ml";;

(* tyins, tmins, flex-flex pairs, restricted list *)
type unifier =
  ((hol_type * hol_type) list * (term * term) list) * (term * term) list * term list;;

let null_unf = (([],[]),[],[] : unifier);;

let safe_tyins i theta =
  i::(map (fun (a,b) -> type_subst [i] a,b) theta);;

let safe_tmins i theta =
  map (fun (a,b) -> beta_eta_term (vsubst [i] a),b) theta;;

(* DONE CHECKING *)
let type_unify (const_ty : string list) =
  let is_free_ty ty =
    match ty with
      Tyvar(name) -> not (mem name const_ty)
    | _ -> false in

  let rec tfree_in t ty =
    if is_vartype ty then Pervasives.compare t ty = 0
    else exists (tfree_in t) (snd (dest_type ty)) in

  let rec unify ty1 ty2 sofar =
    let ty1 = if is_free_ty ty1 then rev_assocd ty1 sofar ty1 else ty1 in
    let ty2 = if is_free_ty ty2 then rev_assocd ty2 sofar ty2 else ty2 in
    let ty1,ty2 = if is_free_ty ty2 then ty2,ty1 else ty1,ty2 in
    if is_free_ty ty1 then
      if is_vartype ty2 then
        if Pervasives.compare ty1 ty2 = 0 then sofar
        else safe_tyins (ty2,ty1) sofar
      else
        let ty2 = type_subst sofar ty2 in
        if tfree_in ty1 ty2 then failwith "type_unify"
        else safe_tyins (ty2,ty1) sofar
    else if is_type ty1 && is_type ty2 then
      let op1,args1 = dest_type ty1 and op2,args2 = dest_type ty2 in
      if op1 = op2 then itlist2 unify args1 args2 sofar
      else failwith "type_unify"
    else if Pervasives.compare ty1 ty2 = 0 then sofar
    else failwith "type_unify" in

  fun obj ->
    let obj = filter (fun (u,v) -> Pervasives.compare u v <> 0) obj in
    let obj1,obj2 = unzip obj in
    itlist2 unify obj1 obj2 [];;

let hol_unify (avoid : string list) (const_ty : string list) (const_var : string list) =

  let vcounter = ref 0 in
  let new_name avoid =
   (vcounter := !vcounter + 1;
    while mem ("z" ^ (string_of_int !vcounter)) avoid do
      vcounter := !vcounter + 1
    done;
    "z" ^ (string_of_int !vcounter)) in

  (*
   * mk_term [x1;x2;x3] t = \x1 x2 x3. t
   * DONE CHECKING
   *)
  let rec mk_term bvars bod =
    match bvars with
      [] -> bod
    | h::t -> mk_abs(h,mk_term t bod) in

  (*
   * Strip off the binder \x where x does not occur in both terms
   * Then do eta-conversion to the remaining part, since bound-vars stripping
   * may generate new eta-redex
   * DONE CHECKING
   *)
  let rec bound_eta_norm (tm1,tm2) : term * term =
    match tm1,tm2 with
      Abs(bv1,bod1),Abs(bv2,bod2) ->
        let bod1,bod2 = bound_eta_norm (bod1,bod2) in
        if not (vfree_in bv1 bod1) && not (vfree_in bv2 bod2) then bod1,bod2
        else (try let f1,x1 = dest_comb bod1 in
                  if Pervasives.compare bv1 x1 = 0 && not (vfree_in bv1 f1) then f1
                  else mk_abs(bv1,bod1)
              with Failure _ -> mk_abs(bv1,bod1)),
             (try let f2,x2 = dest_comb bod2 in
                  if Pervasives.compare bv2 x2 = 0 && not (vfree_in bv2 f2) then f2
                  else mk_abs(bv2,bod2)
              with Failure _ -> mk_abs(bv2,bod2))
    | _ -> tm1,tm2 in

  (* remove unused bvars *)
  let rec remove_dummy_bvar tm =
    match tm with
      Abs(bv,bod) ->
        let bod = remove_dummy_bvar bod in
        if not (vfree_in bv bod) then bod
        else (try let f,x = dest_comb bod in
                  if Pervasives.compare bv x = 0 && not (vfree_in bv f) then f
                  else mk_abs(bv,bod)
              with Failure _ -> mk_abs(bv,bod))
    | _ -> tm in

  (* test whether the head symbol is a free variable of a term
   * DONE CHECKING
   *)
  let head_free (tm : term) : bool =
    let bvars,tm = get_bound tm in
    let hsym = repeat rator tm in
    let name = name_of hsym in
    not (is_const hsym) && not (mem hsym bvars) && not (mem name const_var) && not (has_prefix name "mc") in

  (* get the index of bvar, -1 if not bounded
   * find from the tail, e.g.
   * bindex x [x;x;x] = 2
   * bindex x [x;x;y] = 1
   * bindex x [x;y;y] = 0
   * bindex x [y;y;y] = -1
   * DONE CHECKING
   *)
  let bindex (var : term) (bvars : term list) : int =
    try let ret = index var (rev bvars) in
        (length bvars) - ret - 1
    with Failure "index" -> -1 in

  (* try to check rigid-rigid pairs
   * if rigid head not match then raise exception
   * else return type of pairs of const if type not match
   * DONE CHECKING
   *)
  let rec check_rr (obj : (term * term) list) : (hol_type * hol_type) list =
    match obj with
      (tm1,tm2)::t -> let bv1,(hs1,_) = decompose tm1 and bv2,(hs2,_) = decompose tm2 in
                      let bin1 = bindex hs1 bv1 and bin2 = bindex hs2 bv2 in
                      let rigid1 = is_const hs1 || bin1 >= 0 || (mem (name_of hs1) const_var) || (has_prefix (name_of hs1) "mc") in
                      let rigid2 = is_const hs2 || bin2 >= 0 || (mem (name_of hs2) const_var) || (has_prefix (name_of hs2) "mc") in
                      if rigid1 && rigid2 then
                        if bin1 < 0 && bin2 < 0 then
                          (* constant or const_var *)
                          if is_const hs1 then
                            if is_const hs2 then
                              if name_of hs1 <> name_of hs2 then failwith "check_rr"
                              else (type_of hs1,type_of hs2)::(check_rr t)
                            else failwith "check_rr"
                          else if Pervasives.compare hs1 hs2 <> 0 then failwith "check_rr"
                               else check_rr t
                        else if bin1 <> bin2 then failwith "check_rr"
                             else check_rr t
                      else check_rr t
    | [] -> [] in

  let is_free_var v = is_var v && not (mem (name_of v) const_var) && not (has_prefix (name_of v) "mc") in

  (* each pair of obj must have matched type *)
  let rec work dep avoid (obj : (term * term) list) (rsl : term list) (tyins,tmins) sofar : unifier list =
    if exists (fun (a,b) -> (tm_size a) >= 50) tmins then sofar else
    if exists (fun (a,b) -> (tm_size a) >= 50 || (tm_size b) >= 50) obj then sofar else (
    (* check maximum depth *)
    (*
    List.iter (fun (u,v) -> Printf.printf "0\t%d\t%d\n%!" (tm_size u) (tm_size v)) obj;
    *)
    if dep >= 10 then sofar else
    (* step 0: beta-eta normalization and kill extra bvars *)
    let obj = pmap beta_eta_term obj in
    let obj = map bound_eta_norm obj in
    let rsl = map beta_eta_term rsl in
    let rsl = map remove_dummy_bvar rsl in
    (* step -1: dealing with rsl *)
    try let tm,rsl = pop (fun tm -> not (head_free tm)) rsl in
        let bvs,(hs,args) = decompose tm in
        if is_var hs && has_prefix (name_of hs) "mc" then sofar
        else let rsl = itlist (fun arg t -> (mk_term bvs arg)::t) args rsl in
             work dep avoid obj rsl (tyins,tmins) sofar
    (* TODO connectivity branch prune *)
    with Failure "pop" ->
    (* step D: remove all identical pairs *)
    (*
    List.iter (fun (u,v) -> Printf.printf "1\t%s\t\t\t%s\n%!" (string_of_term u) (string_of_term v)) obj;
    List.iter (fun (u,v) -> Printf.printf "1\t%s\t\t\t%s\n%!" (string_of_type (type_of u)) (string_of_type (type_of v))) obj;
    print_endline "";
    *)
    let obj = filter (fun (u,v) -> alphaorder u v <> 0) obj in
    (* step O: swap all bound-free pairs *)
    let obj = map (fun (u,v) -> if is_free_var v || not (head_free u) && head_free v then (v,u)
                                else (u,v)) obj in
    (* step V: try to find FV-term pair *)
    try let (fv,tm),obj = pop (fun (u,v) -> is_free_var u && not (vfree_in u v)) obj in
        let tmins = safe_tmins (tm,fv) tmins in
        work dep avoid (pmap (vsubst [tm,fv]) obj) (map (vsubst [tm,fv]) rsl) (tyins,tmins) sofar
    with Failure "pop" ->
    (* step T_S: match all types of const head
     * might cause incompleteness here *)
    try 
        let tmp_ins = type_unify const_ty (check_rr obj) in
        if length tmp_ins > 0 then
          let tyins = itlist safe_tyins tmp_ins tyins in
          let tmins = pmap (inst tmp_ins) tmins in
          work dep avoid (pmap (inst tmp_ins) obj) (map (inst tmp_ins) rsl) (tyins,tmins) sofar else
        (* step S: match one rigid-rigid pair *)
        try let (tm1,tm2),obj = pop (fun (u,v) -> not (head_free u)) obj in
            let bv1,(hs1,args1) = decompose tm1 and bv2,(hs2,args2) = decompose tm2 in
            let bv1,bv2,args1,args2 =
              let l1 = length bv1 and l2 = length bv2 in
              if l1 = l2 then bv1,bv2,args1,args2
              else if l1 < l2 then
                let extra = Array.to_list (Array.sub (Array.of_list bv2) l1 (l2-l1)) in
                bv1 @ extra,bv2,args1 @ extra,args2
              else
                let extra = Array.to_list (Array.sub (Array.of_list bv1) l2 (l1-l2)) in
                bv1,bv2 @ extra,args1,args2 @ extra in
            let obj = itlist2 (fun u1 u2 t -> (mk_term bv1 u1,mk_term bv2 u2)::t) args1 args2 obj in
            work dep avoid obj rsl (tyins,tmins) sofar
        with Failure "pop" ->
        try let tm1,tm2 = find (fun (u,v) -> not (head_free v)) obj in
          let bv1,(hs1,args1) = decompose tm1 and bv2,(hs2,args2) = decompose tm2 in
          (* step I: imitation *)
          let sofar =
            if is_const hs2 || (mem (name_of hs2) const_var) || (has_prefix (name_of hs2) "mc") then
              let tyl1,apx1 = dest_fun (type_of hs1) and tyl2,apx2 = dest_fun (type_of hs2) in
              let bvars = map (fun ty -> mk_var(new_name avoid,ty)) tyl1 in
              let args = map (fun ty -> mk_lcomb (mk_var(new_name avoid,mk_fun(tyl1,ty))) bvars) tyl2 in
              let tm = mk_term bvars (mk_lcomb hs2 args) in
              let tmins' = safe_tmins (tm,hs1) tmins in
              work (dep+1) avoid (pmap (vsubst [tm,hs1]) obj) (map (vsubst [tm,hs1]) rsl) (tyins,tmins') sofar
            else sofar in
          (* step T_P and P: projection *)
          let tyl1,apx1 = dest_fun (type_of hs1) in
          let bvars = map (fun ty -> mk_var(new_name avoid,ty)) tyl1 in
          let noname (k : int) sofar =
            let pvar = el k bvars in
            let tyl2,apx2 = dest_fun (type_of pvar) in
            (* unify type apx1 and apx2 *)
            try let tty = type_unify const_ty [apx1,apx2] in
                let args = map (fun ty -> mk_lcomb (mk_var(new_name avoid,mk_fun(tyl1,ty))) bvars) tyl2 in
                let tm = mk_term bvars (mk_lcomb pvar args) in
                let t,x = inst tty tm,inst tty hs1 in
                let tyins' = itlist safe_tyins tty tyins in
                let tmins' = safe_tmins (t,x) (pmap (inst tty) tmins) in
                work (dep+1) avoid (pmap ((vsubst [t,x]) o (inst tty)) obj) (map ((vsubst [t,x]) o (inst tty)) rsl) (tyins',tmins') sofar
            with Failure "type_unify" -> sofar in
          itlist noname (0--((length bvars)-1)) sofar
        with Failure "find" ->
        (* do some cleaning, i.e., remove idendity term instantiation *)
        let tmins = filter (fun (a,b) -> Pervasives.compare a b <> 0) tmins in
        let obj = List.sort_uniq Pervasives.compare obj in
        let rsl = List.sort_uniq Pervasives.compare rsl in
        ((tyins,tmins),obj,rsl)::sofar
    with Failure s when s = "check_rr" || s = "type_unify" -> sofar ) in

  fun (obj : (term * term) list) (rsl : term list) ->
    (* check different vars have different names *)
    let fvars = List.sort_uniq Pervasives.compare (freesl ((let l,r = unzip obj in l @ r) @ rsl)) in
    let fnames = List.sort_uniq Pervasives.compare (map (fun x -> fst (dest_var x)) fvars) in
    if length fvars <> length fnames then failwith "hol_unify[fatal]: different free vars have same name"
    else try let tyins = type_unify const_ty (pmap type_of obj) in
             let obj = pmap (inst tyins) obj in
             let rsl = map (inst tyins) rsl in
             let tmins = map (fun v -> let v' = inst tyins v in v',v') fvars in
             work 0 (union avoid fnames) obj rsl (tyins,tmins) []
         with Failure "type_unify" -> [];;
