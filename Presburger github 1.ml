(*

Algorithm :

Let F be a first-order formula for the Presburger arithmetic

1) Put F on Prenex Normal Form (PNF), yielding

Q1 x1, Q2 x2, ... , Qn xn, F2

2) Put F2 on Negation Normal Form (NNF), yielding

Q1 x1, Q2 x2, ... , Qn xn, F3

3) Normalize F3 to use < as the only comparison operator, yielding

Q1 x1, Q2 x2, ... , Qn xn, F4

4) Put F4 on Conjunctive Normal Form (CNF), yielding

Q1 x1, Q2 x2, ... , Qn xn, F5

5) Reorder quantifiers to obtain a conjunction of first-order formulas.

F is now a conjunction of disjunctions of formulas under the form

Q1 x1, Q2 x2, ... , Qr xr, t1(x1,...,xr)<t2(x1,...,xr)

6) Replace every "Forall xi" with "Not(Exists xi, Not(...))"

7) Verify this formula using automata

-----------------------------------------------------------------------

Through simple manipulations of the original formula, this algorithm
uses the classical method with automata, but the automaton is built
only using the < automaton.
With Step 5), eventually, instead of considering the original formula, we
consider a conjunction of simpler formulas.*);;

(*For now, the only relations this program treats are =,!=,<,<=,>,>=*);;

(*Step 0) : first functions and definitions*);;

(*Definitions*)

type term =
	| Var of int
	| Varm of string (*mute variables (ex.: x)*)
	| Varmneg of string (*Mute variable with a - (ex. : -x).
								 Such signes will be simplified
								 eventually, this is only for
								 temporary convenience*)
	| Fn of string * term list (*n-ary function applied to n terms*);;

type ('a)formula =
	| F
	| T
	| Atom of 'a
	| Not of ('a)formula
	| And of ('a)formula * ('a)formula
	| Or of ('a)formula * ('a)formula
	| Forall of string * ('a)formula
	| Exists of string * ('a)formula;;

type fol = R of string * term list (*A relation between terms.
												 Here, only binary relation will be used*);;

type folformula = fol formula;;

(*Example*)

let h = Forall("x",(Exists("y",Not(Or(Atom(R("=",[Varm "x";Varm "y"])),
												  (Forall("z",Atom(R(">",[Varm "x"; Fn("+",[Varm "z";Var 1])])))))))));;

(*I will use another example, as ths one is not suited to exemplify Step 4)*);;

(*map and mem functions*)

let rec map f l = match l with
	| [] -> []
	| a::b -> (f a)::(map f b);;

let rec mem x l = match l with
	| [] -> false
	| a::b -> (a=x) || (mem x b);;

(*prenex_core returns the core formula of a prenex formula.
It can be used to return the first formula which doesn't begin with a quantifier
when reading any formula*)

let rec prenex_core f = match f with
	| Exists(x,f1) -> prenex_core f1
	| Forall(x,f1) -> prenex_core f1
	| _ -> f;;

(*prenex_first_quants returns the quantifiers of a prenex formula*)

let rec prenex_first_quants f = match f with
	| Exists(x,Exists(y,f1)) -> Exists(x,prenex(Exists(y,f1)))
	| Exists(x,Forall(y,f1)) -> Exists(x,prenex(Forall(y,f1)))
	| Forall(x,Exists(y,f1)) -> Forall(x,prenex(Exists(y,f1)))
	| Forall(x,Forall(y,f1)) -> Forall(x,prenex(Forall(y,f1)))
	| Exists(x,f1) -> Exists(x,T)
	| Forall(x,f1) -> Forall(x,T)
	| _ -> failwith "f should be in PNF";;

(*Change the core of a prenex formula*)

let change_core f second_core =
	let quants = prenex_first_quants f in
	let rec reach_core_and_replace quantifiers core = match quantifiers with
		| Exists(x,T) -> Exists(x,core)
		| Forall(x,T) -> Forall(x,core)
		| Exists(x,q) -> Exists(x, reach_core_and_replace q core)
		| Forall(x,q) -> Forall(x, reach_core_and_replace q core)
		| _ -> failwith "change_core error"
	in
	reach_core_and_replace quants second_core;;

(*Merge sort used in no_double*)

let split l =
    let n = List.length l in 
    let rec aux l acc = match acc with
		| 0 -> ([],l)
		| m -> let (l1,l2) = aux (List.tl (l)) (m-1) in ((List.hd l)::l1,l2)
    in aux l (n/2);;

let rec fusion l1 l2 = match(l1,l2) with
	|([],l) -> l
	|(l,[]) -> l
	|(a::p,b::q) -> if a<b then a::(fusion p (b::q)) else b::(fusion (a::p) q);;

let rec msort l = match l with
	| [] -> l
	| [a] -> [a]
	| l -> let (l1,l2) = split l in fusion (msort l1) (msort l2);;

(*To substract duplicates from unions*)

let no_double l = match l with
	| [] -> []
	| [a] -> [a]
	| _ ->
		let l2 = msort l in
		let a = List.hd(l2) in
		let l3 = List.tl(l2) in
		let rec delete_doubles a li = match li with
			| [] -> []
			| x::b when x = a -> delete_doubles a b
			| x::b -> x::(delete_doubles x b)
		in a::(delete_doubles a l3);;

(*For set operations*)

let rec unions l = match l with (*Doesn't eliminate duplicates*)
	| [] -> []
	| a::b -> a@(unions b);;

let rec remove l x = match l with
	| [] -> []
	| a::b when a = x -> remove b x
	| a::b -> a::(remove b x);;

(*Return free variables*)

let rec fvt t = match t with
	| Var(k) -> []
	| Varm(x) -> [x]
	| Varmneg(x) -> [x]
	| Fn(f,terms) -> unions (map (fvt) (terms));;

let fvf f =
	let rec free_var f = match f with
		| F -> []
		| T -> []
		| Atom(R(g,terms)) -> unions (map fvt terms)
		| Not(f1) -> free_var f1
		| And(f1,f2) -> unions [free_var f1;free_var f2]
		| Or(f1,f2) -> unions [free_var f1;free_var f2]
		| Forall(x,f1) -> remove (free_var f1) x (*x is not free*)
		| Exists(x,f1) -> remove (free_var f1) x (*x is not free*)
	in no_double (free_var f);;


(*Step 1)*);;

(*We assume that if two variables are different then they have different names*)

let rec prenex f = failwith "work in progress";;

(*The formula from the example becomes :*)

Forall("x",
	Exists("y",
		Forall("z",
			Not(Or(Atom(R("=",[Varm "x";Varm "y"])),
					  Atom(R(">",[Varm "x";Varm "z"])))))));;

(*Step 2)*);;

let rec quantifier_free_nnf f = match f with
	| F -> F
	| T -> T
	| Not(F) -> T
	| Not(T) -> F
	| Not(Not(f1)) -> quantifier_free_nnf f1
	| Not(And(f1,f2)) -> Or(quantifier_free_nnf(Not(f1)),quantifier_free_nnf(Not(f2)))
	| And(f1,f2) -> And(quantifier_free_nnf f1, quantifier_free_nnf f2)
	| Not(Or(f1,f2)) -> And(quantifier_free_nnf(Not(f1)),quantifier_free_nnf(Not(f2)))
	| Or(f1,f2) -> Or(quantifier_free_nnf f1, quantifier_free_nnf f2)
	| Not(Atom(_)) -> f
	| Atom(_) -> f
	| _ -> failwith "f should be quantifier free";;

let step2 f =
	let f1 = prenex f in
	change_core f1 (quantifier_free_nnf (prenex_core (f1)));;

(*The formula from the example becomes :*)

Forall("x",
	Exists("y",
		Forall("z",
			And(Not(Atom(R("=",[Varm "x";Varm "y"]))),
				 Not(Atom(R(">",[Varm "x";Fn("+",[Varm "z";Var 1])])))))));;

(*Step 3)*);;

let rec treat r t1 t2 = match r with
	| "=" -> And(Atom(R("<",[t1;Fn("+",[t2;Var 1])])),Atom(R("<",[t2;Fn("+",[t1;Var 1])])))
	| "<" -> Atom(R(r,[t1;t2]))
	| "<=" -> Atom(R("<",[t1;Fn("+",[t2;Var 1])]))
	| ">" -> Atom(R(r,[t2;t1]))
	| ">=" -> Atom(R("<",[t2;Fn("+",[t1;Var 1])]))
	| _ -> failwith "unknown relation";;

let treat_neg r t1 t2 = match r with
	| "=" -> Or(Atom(R("<",[t1;t2])),Atom(R("<",[t2;t1]))) (*Not equal*)
	| "<" -> Atom(R("<",[t2;Fn("+",[t1;Var 1])])) (*Not < is >=*)
	| "<=" -> Atom(R(r,[t2;t1])) (*Not <= is >*)
	| ">" -> Atom(R("<",[t1;Fn("+",[t2;Var 1])])) (*Not > is <=*)
	| ">=" -> Atom(R(r,[t1;t2])) (*Not >= is <*)
	| _ -> failwith "unknown relation";;

let rec quantifier_free_nnf_only_less_than f = match f with
	| F -> f
	| T -> f
	| Atom(R(r,[t1;t2])) -> treat r t1 t2
	| Not(Atom(R(r,[t1;t2]))) -> treat_neg r t1 t2
	| And(f1,f2) -> And(quantifier_free_nnf_only_less_than f1, quantifier_free_nnf_only_less_than f2)
	| Or(f1,f2) -> Or(quantifier_free_nnf_only_less_than f1, quantifier_free_nnf_only_less_than f2)
	| Atom(R(_,_)) -> failwith "non binary relation"
	| Not(Atom(R(_,_))) -> failwith "non binary relation"
	| Not(f1) -> failwith "f should be in nnf"
	| _ -> failwith "f should be quantifier free";;

let step3 f =
	let f1 = step2 f in
	change_core f1 (quantifier_free_nnf_only_less_than (prenex_core (f1)));;

(*The formula from the example becomes :*)

Forall("x",
	Exists("y",
		Forall("z",
			And(Or(Atom(R("<",[Varm "x";Varm "y"])),
					 Atom(R("<",[Varm "y";Varm "x"]))),
				 Atom(R("<",[Varm "x";Fn("+",[Fn("+",[Varm "z";Var 1]);Var 1])]))))));;

(*Step 4)*);;

let rec distribution f1 f2 = match (f1,f2) with
	| (And(f11,f12),_) -> And(distribution f11 f2,distribution f12 f2)
	| (_,And(f21,f22)) -> And(distribution f1 f21,distribution f1 f22)
	| _ -> Or(f1,f2);;

let rec quantifier_free_nnf_cnf f = match f with
	| Or(f1,f2) -> distribution (quantifier_free_nnf_cnf f1) (quantifier_free_nnf_cnf f2)
	| And(f1,f2) -> And(quantifier_free_nnf_cnf f1,quantifier_free_nnf_cnf f2)
	| _ -> f;;

let step4 f =
	let f1 = step3 f in
	change_core f1 (quantifier_free_nnf_cnf (prenex_core (f1)));;

(*The formula from the example becomes :*)

(*Example isn't convenient. I will chose another*);;

(*Step 5)*);;

let prenex_quantlist f = (*lists the quantifiers of a prenex formula*)
	let quants = ref [] in
	let rec search f = match f with
		| Exists(x,f1) -> quants := (Exists(x,T))::(!quants) ; search f1
		| Forall(x,f1) -> quants := (Forall(x,T))::(!quants) ; search f1
		| _ -> ()
	in
	search f;
	!quants;;

let good_quants quants f =
	let f1 = ref f in
	let freevars = fvf f in
	let rec choice q = match q with
		| [] -> ()
		| Exists(x,_)::b -> if mem x freevars then f1 := Exists(x,(!f1)) ; choice b
		| Forall(x,_)::b -> if mem x freevars then f1 := Forall(x,(!f1)) ; choice b
		| _ -> failwith "good_quants error"
	in
	choice quants;
	!f1;;

let reorder_quant f =
	let core = prenex_core f in
	let quants = prenex_quantlist f in
	let rec treat_core form = match form with
		| F -> form
		| T -> form
		| Atom(_) -> good_quants quants form
		| Not(form1) -> Not(treat_core form1)
		| And(f1,f2) -> And(treat_core f1, treat_core f2)
		| Or(f1,f2) -> Or(treat_core f1, treat_core f2)
		| _ -> failwith "treat_core error"
	in
	treat_core core;;

let step5 f = reorder_quant (step4 f);;

(*Step 6)*);;

let rec only_exists f = match f with
	| Exists(x,f1) -> Exists(x,only_exists f1)
	| Forall(x,f1) -> Not(Exists(x,Not(only_exists f1)))
	| Not(f1) -> Not(only_exists f1)
	| And(f1,f2) -> And(only_exists f1,only_exists f2)
	| Or(f1,f2) -> Or(only_exists f1,only_exists f2)
	| _ -> f;;

let step6 f = only_exists (step5 f);;

(*Step 7)*);;

(*Convertion*)

let div_by_2 k = k/2;;

let rec all_zeros l = match l with (*There must be a better way*)
	| [] -> true
	| a::b -> (a=0)&&(all_zeros b);;

let convert2 l =
	let l2 = ref [] in
	let rec convertion l =
		if all_zeros l then ()
		else
			let rec treat li = match li with
				| [] -> []
				| a::b -> (a mod 2)::(treat b)
			in
			l2 := treat l::(!l2);
			convertion (map div_by_2 l);
	in
	convertion l;
	!l2;;

(*Automats*)

type automat = {
	state_nbr : int;
	transitions : int -> int list -> int;
	initial : int;
	accepting : int list;
	};;

let run_automat a m =
	let rec running aut state word = match word with
		| [] -> state
		| u::v -> running aut (aut.transitions state u) v
	in
	running a (a.initial) m;;

let accepted a m = mem (run_automat a m) (a.accepting);;

(*<*)

let strict_inf_transi k u =
	let from0 v = match v with
		| [1;1] -> 0
		| [0;0] -> 0
		| [0;1] -> 1
		| _ -> failwith "block"
	in
	let from1 v = 1 in
	match k with
		| 0 -> from0 u
		| 1 -> from1 u
		| _ -> failwith "strict_inf_transi error";;

let strict_inf_automat = {state_nbr = 2; transitions = strict_inf_transi; initial = 0; accepting = [1]};;

(*Running this automat returns true if x<y, "block" if x>y, false if x=y*);;

accepted strict_inf_automat (convert2 [3;4]);;





(*Work in progress : first ideas to simplify terms so that
Fn("+",[Var 3;Var 4;Varm "x";Var 5;Varm "y"])
becomes
Fn("+",[Var 12;Varm "x";Varm "y"])
*);;

let rec order_vars terms =
	let lv = ref [] in
	let lvm = ref [] in
	let lvmn = ref [] in
	let lfn = ref [] in
	let rec treatment tl = match tl with
		| [] -> ()
		| Var(k)::b -> lv := Var(k)::(!lv) ; treatment b
		| Varm(x)::b -> lvm := Varm(x)::(!lvm) ; treatment b
		| Varmneg(x)::b -> lvmn := Varmneg(x)::(!lvmn) ; treatment b
		| Fn(g,tl2)::b -> lfn := (Fn(g, order_vars tl2))::(!lfn) ; treatment b
	in
	treatment terms;
	(!lv)@(!lvm)@(!lvmn)@(!lfn);;

order_vars [Var(2);Varm("x");Var(3);Fn("=",[Var(4);Varm("y");Var(5)]);Varmneg("z")];;

(*ISSUE : can't reorder this way with "-"*);;

let rec simplify_term t = match t with 
	| Fn("+",terms) -> (*Sum until a Varm is reached, continue.
								To be applied until len(terms) = 1 + len(unions fvt terms)*)
	| Fn("-",terms) -> 
	| _ -> t;;


(*Probably bad ideas*)


let group_int_var_sum tlist =
	let acc = ref 0 in
	let rec no_int_sum tl = match tl with
		| [] -> []
		| (Var(k))::b -> acc := !acc+k ; no_int_sum b
		| t::b -> t::no_int_sum b
	in
	Fn("+",Var(!acc)::(no_int_sum tlist));;

let group_int_var_sub tlist = (*issues here*)
	let acc = ref 0 in
	let first_is_mute = ref false in
	let rec no_int_sub tl cond = match tl with
		| [] -> []
		| (Var(k))::b when cond=false -> acc := k ; no_int_sub b true
		| (Varm(x))::b when cond = false -> first_is_mute := true ; (Varm(x))::(no_int_sub b true)
		| (Varmneg(x))::b when cond = false -> first_is_mute := true ; (Varmneg(x))::(no_int_sub b true)
		| (Var(k))::b -> acc := !acc-k ; no_int_sub b cond
		| (Varm(x))::b -> Varmneg(x)::(no_int_sub b cond)
		| (Varmneg(x))::b -> Varm(x)::(no_int_sub b cond)
		| t::b -> no_int_sub b cond
	in
	if !first_is_mute = true then
		Fn("-",(no_int_sub tlist false)@[Var(!acc)])(*ugly but... ?*)
	else
		Fn("-",Var(!acc)::(no_int_sub tlist false));;

(*Same must be done to regroup the x. Do it at the same time ?*)