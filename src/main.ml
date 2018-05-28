open List;;

(* SECD MACHINE *)

type answer = Const' of int  | T' | F' | Tuple' of answer list | VClosure of table * string * opcode list and
table = (string * answer) list and
def = DefinedAs of string * exp | OneThenAnother of def * def | Parallel of def * def (* | LocalIn of def * def  *)and
exp =
	Const of int
   | Abs of exp
   | Var of string
   | Plus of exp * exp
   | Minus of exp * exp
   | Times of exp * exp
   | Div of exp * exp
   | Mod of exp * exp
   | Expo of exp * exp
   | Equal of exp * exp
   | Gt of exp * exp
   | Lt of exp * exp
   | Ge of exp * exp
   | Le of exp * exp
   | T | F
   | Not of exp
   | And of exp * exp
   | Or of exp * exp
   | Implies of exp * exp
   | Tuple of exp list
   | Proj of exp * exp
   | Lambda of string * exp (*new exps from here*)
   | FunctionCall of exp * exp 
   | If_Then_Else of exp * exp * exp 
   | Let of def * exp

and opcode = CONST of int
			| ABS
			| PLUS
			| MINUS
			| TIMES
			| DIV
			| MOD
			| EXPO
			| EQUAL
			| GREATER
			| LESSER
			| GREATEROREQUAL
			| LESSEROREQUAL
			| NOT
			| AND
			| OR
			| IMPLIES
			| TRUE
			| FALSE
			| LOOKUP of string
			| TUPLE of int
			| PROJ
			| CLOS of string * opcode list
			| RET
			| APP
			| COND of opcode list * opcode list
			| BIND of string
			| UNBIND of string;; 

let rec dv d = match d with
		DefinedAs(x, e1) -> [x]
	| OneThenAnother(d1, d2) -> dv(d1)@dv(d2)
	| Parallel(d1, d2) -> dv(d1)@dv(d2);;
(* 	| LocalIn(d1, d2)-> dv(d2);;
 *)
let rec checkPresent a l = match l with
		[] -> false
	|	x::xs -> if(x=a) then true 
					else checkPresent a xs;;

exception CONTRADICTORYDEFINITIONS;;
let rec intersectionOfListsEmpty l1 l2 = match l1 with
		[] -> true
	|	x::xs -> if (checkPresent x l2) = true then false
					else intersectionOfListsEmpty xs l2;; 


let rec unbindlist l = match l with
		[] -> []
		| x::xs -> [UNBIND(x)]@(unbindlist xs);;

(* let rec unbindsecondopcode l = match l with
	 []] -> []
	| x::xs -> UNBINDSECOND
 *)

let rec compile e =
	let rec elaborateOpcode d = match d with
 		  DefinedAs(x, e1) -> compile(e1)@[BIND(x)]
 		| OneThenAnother(d1, d2) -> elaborateOpcode(d1)@elaborateOpcode(d2)
 		| Parallel(d1, d2) -> if(intersectionOfListsEmpty (dv d1) (dv d2))=true then elaborateOpcode(d1)@elaborateOpcode(d2) else raise CONTRADICTORYDEFINITIONS
 		(* | LocalIn(d1, d2) -> elaborateOpcode(d1)@elaborateOpcode(d2)@[UNBINDSECOND()] *) in
match e with
   Const n -> [CONST(n)]
 | Abs n -> (compile n)@[ABS]
 | Plus(e1,e2) -> (compile e1)@(compile e2)@[PLUS]
 | Minus(e1,e2) -> (compile e1)@(compile e2)@[MINUS]
 | Times(e1,e2) -> (compile e1)@(compile e2)@[TIMES]
 | Div(e1,e2) -> (compile e1)@(compile e2)@[DIV]
 | Mod(e1,e2) -> (compile e1)@(compile e2)@[MOD]
 | Expo(e1,e2) -> (compile e1)@(compile e2)@[EXPO]
 | Equal(e1,e2) -> (compile e1)@(compile e2)@[EQUAL]
 | Gt(e1,e2) -> (compile e1)@(compile e2)@[GREATER]
 | Lt(e1,e2) -> (compile e1)@(compile e2)@[LESSER]	
 | Ge(e1,e2) -> (compile e1)@(compile e2)@[GREATEROREQUAL]
 | Le(e1,e2) -> (compile e1)@(compile e2)@[LESSEROREQUAL]
 | Not e1 -> (compile e1)@[NOT]
 | And(e1,e2) -> (compile e1)@(compile e2)@[AND]
 | Or(e1,e2) -> (compile e1)@(compile e2)@[OR]
 | Implies(e1,e2) -> (compile e1)@(compile e2)@[IMPLIES]
 | T -> [TRUE]
 | F -> [FALSE]
 | Var x -> [LOOKUP(x)]
 | Tuple(l) -> let rec compileOnTuple l = match l with
 					[] -> []
 				| x::xs -> (compile x)@(compileOnTuple xs) in
 				(compileOnTuple l)@[TUPLE(length l)]
 | Proj(i,tuple) -> (compile tuple)@compile(i)@[PROJ]

 | Lambda(x, e') -> [CLOS(x, compile(e')@[RET])]
 | FunctionCall(e1, e2) -> compile(e1)@compile(e2)@[APP]
 | If_Then_Else(e0, e1, e2) -> compile(e0)@[COND(compile(e1), compile(e2))]
 | Let(d,e) -> elaborateOpcode(d)@compile(e)@unbindlist(dv(d));;

let extract n = match n with
	Const' a -> a;;

let rec exponential (x,n) y = match n with
	0 -> y
   | _ -> if(n>0) then exponential (x,n-1) (y*x) else 0;;


exception VARIABLENOTFOUND;;
let rec find x t = match t with
	[] -> raise VARIABLENOTFOUND
 | (str, ans)::ms -> if x = str then ans else find x ms;;

type stack = answer list;;
type dump = (stack* table* opcode) list;;

let rec execute (s,t,c,d) = match (s,t,c,d) with
   (s, t, [], d) -> hd s
 | (s, t, CONST(n)::c', d) -> execute ((Const'(n))::s, t, c', d)
 | (s, t, LOOKUP(x)::c', d) -> execute ((find x t)::s, t, c', d)
 | (n::s, t, ABS::c', d) -> if (extract n)>0 then execute (n::s, t, c', d) else execute (Const'(-(extract n))::s, t, c', d)
 | (n2::n1::s', t, PLUS::c', d) -> execute ((Const'((extract n1)+(extract n2)))::s', t, c', d)
 | (n2::n1::s', t, MINUS::c', d) -> execute ((Const'((extract n1)-(extract n2)))::s', t, c', d)
 | (n2::n1::s', t, TIMES::c', d) -> execute ((Const'((extract n1)*(extract n2)))::s', t, c', d)
 | (n2::n1::s', t, DIV::c', d) -> execute ((Const'((extract n1)/(extract n2)))::s', t, c', d)
 | (n2::n1::s', t, MOD::c', d) -> execute ((Const'((extract n1) mod (extract n2)))::s', t, c', d)
 | (n2::n1::s', t, EXPO::c', d) -> execute ((Const'(exponential((extract n1),(extract n2)) 1))::s', t, c', d)
 | (n2::n1::s', t, EQUAL::c', d) -> if (extract n1)=(extract n2) then execute (T'::s', t, c', d) else execute (F'::s', t, c', d)
 | (n2::n1::s', t, GREATER::c', d) -> if (extract n1)>(extract n2) then execute (T'::s', t, c', d) else execute (F'::s', t, c', d)
 | (n2::n1::s', t, LESSER::c', d) -> if (extract n1)<(extract n2) then execute (T'::s', t, c', d) else execute (F'::s', t, c', d)
 | (n2::n1::s', t, GREATEROREQUAL::c', d) -> if (extract n1)>=(extract n2) then execute (T'::s', t, c', d) else execute (F'::s', t, c', d)
 | (n2::n1::s', t, LESSEROREQUAL::c', d) -> if (extract n1)<=(extract n2) then execute (T'::s', t, c', d) else execute (F'::s', t, c', d)
 | (n::s', t, NOT::c', d) -> if n=F' then execute (T'::s', t, c', d) else execute (F'::s', t, c', d)
 | (n2::n1::s', t, AND::c', d) -> if n1=T' && n2=T' then execute (T'::s', t, c', d) else execute (F'::s', t, c', d)
 | (n2::n1::s', t, OR::c', d) -> if n1=T' || n2=T' then execute (T'::s', t, c', d) else execute (F'::s', t, c', d)
 | (n2::n1::s', t, IMPLIES::c', d) -> if n1=T' && n2=F' then execute (F'::s', t, c', d) else execute (T'::s', t, c', d)
 | (s, t, TRUE::c', d) -> execute(T'::s, t, c', d)
 | (s, t, FALSE::c', d) -> execute(F'::s, t, c', d)
 | (s, t, TUPLE(n)::c', d) -> let rec extr s (tuplist,s') n = match n with
 							0 -> (tuplist,s')
						  | _ -> extr (tl s) (([hd s]@tuplist),(tl s)) (n-1) in
 							let (tuplist, s') = extr s ([],s) n in
 							execute([Tuple'(tuplist)]@s' , t, c', d)
 | (n::(Tuple'(lis))::s, t, PROJ::c', d) -> let rec foo l i = match i with
					   		0 -> hd l
					   	  | _ -> foo (tl l) (i-1) and
					   		foo2 n = match n with
					   		Const' i -> i in
					   		execute((foo lis (foo2 n))::s, t, c', d)

 | (s, t, CLOS(x, compile_e')::c', d) -> execute((VClosure(t, x, compile_e'))::s, t, c', d)
 | (a::(VClosure(t', x, compile_e'))::s, t, APP::c', d) -> execute([], (x,a)::t', compile_e'@c', (s,t,c')::d)
 | (a::s', t'', RET::c'', (s,t,c')::d) -> execute(a::s, t, c', d)
 | (T'::s, t, COND(c', c'')::c''', d) -> execute(s, t, c'@c''', d)
 | (F'::s, t, COND(c', c'')::c''', d) -> execute(s, t, c''@c''', d)
 | (a::s, t, BIND(x)::c, d) -> execute(s, (x,a)::t, c, d)
 | (s, t, UNBIND(x)::c, d) -> let rec unbind l1 x l2 = match l2 with
 								[] -> []
 							| (str, ans)::tl -> if str = x then l1@tl
 												else unbind (l1@[(str, ans)]) x tl in
 								execute(s, unbind [] x t, c, d);;

(* Examples *)
let e1 = FunctionCall(Lambda("x", Var("x")), Const(1));;
let compile_e1 = compile e1;;
execute([], [], compile_e1, []);;

let e2 = FunctionCall(Lambda("x", Var("x")), Plus(Const(1), Const(1)));;
let compile_e2 = compile e2;;
execute([], [], compile_e2, []);;

let e3 = Let(DefinedAs("x", Const(10)), FunctionCall(Lambda("x", Var("x")), Plus(Const(1), Const(1))));;
let compile_e3 = compile e3;;
execute([], [], compile_e3, []);;

let e4 = FunctionCall(Lambda("x", (Let(DefinedAs("x", Const(10)),Var("x")))), Plus(Const(1), Const(1)));;
let compile_e4 = compile e4;;
execute([], [], compile_e4, []);;

let e5 = If_Then_Else(T, Times(Const(7), Const(8)), Minus(Const(0), Const(5)));;
let compile_e5 = compile e5;;
execute([], [], compile_e5, []);;

let e6 = Let(OneThenAnother(DefinedAs("x", T),DefinedAs("y", F)), And(Var "x", Not(Var "y")));;
let compile_e6 = compile e6;;
execute([], [], compile_e6, []);;


(* **************************************************************************************************************************************** *)


 (* Krivine MACHINE *)

type table = Table of (string * (table * exp)) list and
	 def = DefinedAs of string * exp | OneThenAnother of def * def | Parallel of def * def (* | LocalIn of def * def  *)and
	 exp =
		Const of int
	   | Abs of exp
	   | Var of string
	   | Plus of exp * exp
	   | Minus of exp * exp
	   | Times of exp * exp
	   | Div of exp * exp
	   | Mod of exp * exp
	   | Expo of exp * exp
	   | Equal of exp * exp
	   | Gt of exp * exp
	   | Lt of exp * exp
	   | Ge of exp * exp
	   | Le of exp * exp
	   | Tuple of exp list
   	   | Proj of int * exp
   	   | T | F
	   | Not of exp
	   | And of exp * exp
	   | Or of exp * exp
	   | Implies of exp * exp
	   | Lambda of string * exp (*new exps from here*)
	   | FunctionCall of exp * exp 
	   | If_Then_Else of exp * exp * exp 
	   | Let of def * exp
	   | VClosure of table * exp;;

exception NOTFOUND;;

let rec exponential (x,n) y = match n with
	0 -> y
   | _ -> if(n>0) then exponential (x,n-1) (y*x) else 0;;

let tab t = match t with
		Table t' -> t';;

let rec lookup a t = match tab t with
		[] -> raise NOTFOUND
	| (str, clos)::xs -> if (str = a) then clos else lookup a (Table (xs));;


exception TYPE_MISMATCH_or_UNBOUNDED_VALUE;;

let rec execute  (clos, stackOfClos) = match (clos, stackOfClos) with
	  ((t, Var(x)), stackOfClos) -> execute ((lookup x t), stackOfClos)
	| ((t, Lambda(x, e1')), cl::stackOfClos) -> execute ((Table((x, cl)::(tab t)), e1'), stackOfClos)
	| ((t, FunctionCall(e1, e2)), stackOfClos) -> execute ((t, e1), (t, e2)::stackOfClos)
	| ((t, Const(n)), stackOfClos) -> Const(n)
	| ((t, T), stackOfClos) -> (match stackOfClos with
													[] -> T
												| cl1::cl2::tl -> execute(cl1, tl)
								)
	| ((t, F), stackOfClos) -> (match stackOfClos with
													[] -> F
												| cl1::cl2::tl -> execute(cl2, tl)
								)
	| ((t, If_Then_Else(e0, e1, e2)), stackOfClos) -> execute ((t, e0), (t, e1)::(t, e2)::stackOfClos)
	| ((t, Abs n), stackOfClos) -> let absC t a = match execute ((t, a), stackOfClos) with
	  				Const(b) -> Const (abs b)
	  					 | _ -> raise TYPE_MISMATCH_or_UNBOUNDED_VALUE in
  			 		absC t n
    | ((t, Plus(e1,e2)), stackOfClos) -> let pl a b = match (execute  ((t, a), stackOfClos), execute ((t, b), stackOfClos))with
  					(Const(n1),Const(n2)) -> Const(n1+n2)
  									  | _ -> raise TYPE_MISMATCH_or_UNBOUNDED_VALUE in
  				   pl e1 e2
  	| ((t, Minus(e1,e2)), stackOfClos) -> let mi a b = match (execute  ((t, a), stackOfClos), execute ((t, b), stackOfClos)) with
  					(Const(n1),Const(n2)) -> Const(n1-n2)
  									  | _ -> raise TYPE_MISMATCH_or_UNBOUNDED_VALUE in
  				   mi e1 e2
  	| ((t, Times(e1,e2)), stackOfClos) -> let ti a b = match (execute  ((t, a), stackOfClos), execute ((t, b), stackOfClos)) with
  					(Const(n1),Const(n2)) -> Const(n1*n2)
  									  | _ -> raise TYPE_MISMATCH_or_UNBOUNDED_VALUE in
  				   ti e1 e2
  	| ((t, Div(e1,e2)), stackOfClos) -> let div a b = match (execute  ((t, a), stackOfClos), execute ((t, b), stackOfClos)) with
  					(Const(n1),Const(n2)) -> Const(n1/n2)
  									  | _ -> raise TYPE_MISMATCH_or_UNBOUNDED_VALUE in
  				   div e1 e2
  	| ((t, Mod(e1,e2)), stackOfClos) -> let mo a b = match (execute  ((t, a), stackOfClos), execute ((t, b), stackOfClos)) with
  					(Const(n1),Const(n2)) -> Const(n1 mod n2)
  									  | _ -> raise TYPE_MISMATCH_or_UNBOUNDED_VALUE in
  				   mo e1 e2
    | ((t, Expo(e1,e2)), stackOfClos) -> let foo a b = match (execute  ((t, a), stackOfClos), execute ((t, b), stackOfClos)) with
  					(Const(n1),Const(n2)) -> (n1,n2)
  									  | _ -> raise TYPE_MISMATCH_or_UNBOUNDED_VALUE in
  					Const(exponential (foo e1 e2) 1)
   	| ((t, Equal(e1,e2)), stackOfClos) -> if (execute ((t, e1), stackOfClos) )=(execute ((t, e2), stackOfClos) ) then T else F
   	| ((t, Gt(e1,e2)), stackOfClos) -> let foo a b = match (execute  ((t, a), stackOfClos), execute ((t, b), stackOfClos)) with
  					(Const(n1),Const(n2)) -> (n1,n2)
  									  | _ -> raise TYPE_MISMATCH_or_UNBOUNDED_VALUE in 
  					let (x,y) = foo e1 e2 in
  					if x>y then execute((t, T), stackOfClos) else execute((t, F), stackOfClos)
   	| ((t, Lt(e1,e2)), stackOfClos) -> let foo a b = match (execute  ((t, a), stackOfClos), execute ((t, b), stackOfClos)) with
  					(Const(n1),Const(n2)) -> (n1,n2)
  									  | _ -> raise TYPE_MISMATCH_or_UNBOUNDED_VALUE in
  				 let (x,y) = foo e1 e2 in
  					if x<y then T else F
   	| ((t, Ge(e1,e2)), stackOfClos) -> let foo a b = match (execute  ((t, a), stackOfClos), execute ((t, b), stackOfClos)) with
  					(Const(n1),Const(n2)) -> (n1,n2)
  									  | _ -> raise TYPE_MISMATCH_or_UNBOUNDED_VALUE in
  				 let (x,y) = foo e1 e2 in
  					if x>=y then T else F
   	| ((t, Le(e1,e2)), stackOfClos) -> let foo a b = match (execute  ((t, a), stackOfClos), execute ((t, b), stackOfClos)) with
  					(Const(n1),Const(n2)) -> (n1,n2)
  									  | _ -> raise TYPE_MISMATCH_or_UNBOUNDED_VALUE in
  				 let (x,y) = foo e1 e2 in
  					if x<=y then T else F
  	| ((t, Tuple(lis)), stackOfClos) -> let rec executeOnTuple l = match l with
   						[] -> []
   					| x::xs -> [execute ((t,x), stackOfClos)]@(executeOnTuple xs) in
   				 Tuple(executeOnTuple lis)
    | ((t, Proj(i, tuple)), stackOfClos) -> let rec projection l i = match i with
					   		0 -> hd l
					   	| _ -> projection (tl l) (i-1) and
					   extr tuple = match tuple with
					 	Tuple(l) -> l in
					 execute ((t, (projection (extr tuple) i)), stackOfClos)
   | ((t, Not(e)), stackOfClos) -> if (execute ((t, e), stackOfClos))= T then F else T
   | ((t, And(e1,e2)), stackOfClos) -> if (execute ((t, e1), stackOfClos))=T && (execute ((t, e2), stackOfClos))=T then T else F
   | ((t, Or(e1,e2)), stackOfClos) -> if (execute ((t, e1), stackOfClos))=T || (execute ((t, e2), stackOfClos))=T then T else F
   | ((t, Implies(e1,e2)), stackOfClos) -> if (execute ((t, e1), stackOfClos))=T && (execute ((t, e2), stackOfClos))=F then F else T


  	| ((t, Let(d, e)), stackOfClos) ->  match d with
  						DefinedAs(str, e1) -> execute((t, FunctionCall(Lambda(str,e),e1)), stackOfClos);;


(* Examples *)
let clos1 = (Table([]), FunctionCall(Lambda("x", Var("x")), Const(1)));;
execute (clos1, []);;

let clos2 = (Table([]), FunctionCall(Lambda("x", Var("x")), Plus(Const(1), Const(1))));;
execute (clos2, []);;

let exp = Let(DefinedAs("x", Const(10)), FunctionCall(Lambda("x", Var("x")), Plus(Const(1), Const(1))));;

let clos3 = (Table([]), exp);;

execute (clos3, []);;

let exp2 = FunctionCall(Lambda("x", (Let(DefinedAs("x", Const(10)),Var("x")))), Plus(Const(1), Const(1)));;

let clos4 = (Table([]), exp2);;

execute (clos4, []);;

let clos5 = (Table [], If_Then_Else(T, Times(Const(7), Const(8)), Minus(Const(0), Const(5))));;

execute (clos5, []);;
