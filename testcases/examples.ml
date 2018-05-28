(*
 * Note: you need to change the following datatype and expressions as per your Minusmitted code
 * Please do the changes before you come for demo.
 *)

datatype exp = Const of int
			| T|F
			| Var of string
			| List of exp list
			| Plus of exp * exp
			| Minus of exp * exp
			| Times of exp * exp
			| Div of exp * exp
			| Tuple of exp list
			| Proj of exp * int
			| Gt of exp * exp
			| Lsr of exp * exp
			| Eql of exp * exp
			| If_Then_Else of exp * exp * exp
			| Lambda of exp * exp
			| FunctionCall of exp * exp
			| Let of exp * exp
			| DefinedAs of exp * exp
			| OneThenAnother of exp list
			| Parallel of exp list
			| Localinend of exp list * exp
			| Dec of exp list
			| CTuple of closure list
			| At of int
			| Bind of exp
			
			| Restp of exp
			| Tothisp of exp
			| Rests of exp
			| Tothiss of exp
			| Restm of exp
			| Tothism of exp
			| Restd of exp
			| Tothisd of exp
			| Restg of exp
			| Tothisg of exp
			| Restl of exp
			| Tothisl of exp
			| Reste of exp
			| Tothise of exp
			| Ifthn of exp * exp
			| Lets of exp*exp
			and
			closure = ACL of (exp * closure) list * exp

krivine:-

execute((Table [],FunctionCall(
								FunctionCall(
										Lambda("x", Plus(Var("x"), Const(2))),
										Lambda("d",Times(Var("d"),Const(2))) 
								),
					Const(2))
),[]);;


execute((Table [("z",(Table [],Const(3)))],Var("z")),[]);;

execute((Table [],Plus(Plus(Const(2),Const(3)),Plus(Const(2),Const(3)))),[]);;

execute((Table ["z",(Table [],Const(3))],Plus(Const(2),Var("z"))),[]);;

execute((Table [],FunctionCall(Lambda("x",Plus(Var("x"),Const(1))),Const(2))),[]);;

execute((Table [],FunctionCall(Lambda("x",Times(Var("x"),Plus(Var("x"),Const(1)))),Const(2))),[]);;

execute((Table [],FunctionCall(Lambda("x",FunctionCall(Lambda("d",Times(Var("d"),Const(2))),Const(2))),Const(2))),[]);;

//execute((Table [],If_Then_Else(Gt(Const(8),Const(2)),FunctionCall(Lambda("x",Div(Var("x"),Const(2))),Const(2)),FunctionCall(Lambda("x",Times(Var("x"),Plus(Var("x"),Const(1)))),Const(2)))),[]);;

//execute((Table [],If_Then_Else(Gt(Const(1),Const(2)),FunctionCall(Lambda("x",Div(Var("x"),Const(2))),Const(2)),FunctionCall(Lambda("x",Times(Var("x"),Plus(Var("x"),Const(1)))),Const(2)))),[]);;

execute((Table [],Let(DefinedAs("a",Const(2)),Plus(Var("a"),Const(20)))),[]);;

execute((Table [],Proj(2, Tuple([Const(1);Const(2);Const(3)]))),[]);;

execute((Table [],FunctionCall(Lambda("x",Let(DefinedAs("a",Const(2)),Plus(Var("a"),Var("x")))),Const(2))),[]);;

SECDmachine:-

let e1 = compile(Proj(Const(2),Tuple([Const(12);Const(121);Const(33)])));;
execute([], [],e1, []);;

let e2 = compile(Let(Parallel(DefinedAs("a",Const(1)),Parallel(DefinedAs("b",Const(2)),DefinedAs("c",Const(3)))),Plus(Plus(Var("a"),Var("b")),Times(Var("c"),Const(2)))));;
execute([], [], e2, []);;

let e3 = compile(If_Then_Else(Gt(Const(4),Const(2)),Plus(Const(1),Const(3)),Minus(Const(1),Const(3))));;
execute([], [], e3, []);;

let e4 = compile(Let(OneThenAnother(DefinedAs("f",F),OneThenAnother(DefinedAs("a",Const(1)),OneThenAnother(DefinedAs("b",Const(2)),DefinedAs("c",Const(3))))),
	Plus(Plus(Var("a"),Var("b")),Times(Var("c"),Const(2)))));;
execute([], [], e4, []);;

let e5 = compile(FunctionCall(Lambda("x",Plus(Var("x"),Const(1))),Const(2)));;
execute([], [], e5, []);;

let e6 = compile(FunctionCall(Lambda("x",Times(Var("x"),Plus(Var("x"),Const(1)))),Const(2)));;
execute([], [], e6, []);;

let e7 = compile(FunctionCall(
								FunctionCall(
										Lambda("x", Plus(Var("x"), Const(2))),
										Lambda("d",Times(Var("d"),Const(2))) 
								),
					Const(2))
				);;
execute([], [], e7, []);;

let e8 = compile(Let(DefinedAs("a",Let(DefinedAs("a",Const(1)),FunctionCall(Lambda("x",Plus(Var("x"),Const(1))),Var("a")))),
	Plus(Var("a"),Const(1))));;
execute([], [], e8, []);;
