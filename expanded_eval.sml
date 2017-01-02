(*
This is a boolean expression parser, simplifier and evaluator.

It deals with the following syntax

<logic> ::= <disj>

<disj> ::= <conj>
<disj> ::= <conj> <disj'>

<disj'> ::= or <disj>

<conj> ::= <atom>
<conj> ::= <atom> <conj'>

<conj'> ::= and <conj>

<atom> ::= not <atom>
<atom> ::= (<logic>)
<atom> ::= True
<atom> ::= False
<atom> ::= <name>
<atom> ::= <variable>

<expr> ::= simplify <logic>
<expr> ::= <logic>

val <variable> = <expr>

print_value <expr>
print_tree <expr>
print_table <expr>

You do not need spaces in between parenthesis or equal signs and other words.

Note that it is very flexible in what can be defined as a variable or
a name. For instance you can define a variable as "print_table" or a name
as "and" (and vice versa) and so far I have not been able to contrive any examples of
where this does not work well (otherwise good syntax fails). However, bad syntax
will give very odd errors and do odd things and so you might want to avoid such
practices.

Example File:

val oneLook = (lookahead and one)
val tokenize = state_mach and not slow and (simple or not oneLook)
val pars = tokenize and oneLook
val evalu = pars and (interpreter and not slow)
print_value evalu
print_tree evalu
print_table evalu
val simp = simplify evalu
print_value simp
print_tree simp

Output:
(((state_mach and (not slow and (simple or not (lookahead and one)))) and (lookahead and one)) and (interpreter and not slow))
			state_mach = T
		 and
				slow = F
			 and
					simple = T
				 or
						lookahead = F
					 and
						one = F
	 and
			lookahead = T
		 and
			one = T
 and
		interpreter = T
	 and
		slow = F
state_mach|slow|simple|lookahead|one|interpreter||(((state_mach and (not slow and (simple or not (lookahead and one)))) and (lookahead and one)) and (interpreter and not slow))
         T|   T|     T|        T|  T|          T||F
         F|   T|     T|        T|  T|          T||F
         T|   F|     T|        T|  T|          T||T
         F|   F|     T|        T|  T|          T||F
         T|   T|     F|        T|  T|          T||F
         F|   T|     F|        T|  T|          T||F
         T|   F|     F|        T|  T|          T||F
         F|   F|     F|        T|  T|          T||F
         T|   T|     T|        F|  T|          T||F
         F|   T|     T|        F|  T|          T||F
         T|   F|     T|        F|  T|          T||F
         F|   F|     T|        F|  T|          T||F
         T|   T|     F|        F|  T|          T||F
         F|   T|     F|        F|  T|          T||F
         T|   F|     F|        F|  T|          T||F
         F|   F|     F|        F|  T|          T||F
         T|   T|     T|        T|  F|          T||F
         F|   T|     T|        T|  F|          T||F
         T|   F|     T|        T|  F|          T||F
         F|   F|     T|        T|  F|          T||F
         T|   T|     F|        T|  F|          T||F
         F|   T|     F|        T|  F|          T||F
         T|   F|     F|        T|  F|          T||F
         F|   F|     F|        T|  F|          T||F
         T|   T|     T|        F|  F|          T||F
         F|   T|     T|        F|  F|          T||F
         T|   F|     T|        F|  F|          T||F
         F|   F|     T|        F|  F|          T||F
         T|   T|     F|        F|  F|          T||F
         F|   T|     F|        F|  F|          T||F
         T|   F|     F|        F|  F|          T||F
         F|   F|     F|        F|  F|          T||F
         T|   T|     T|        T|  T|          F||F
         F|   T|     T|        T|  T|          F||F
         T|   F|     T|        T|  T|          F||F
         F|   F|     T|        T|  T|          F||F
         T|   T|     F|        T|  T|          F||F
         F|   T|     F|        T|  T|          F||F
         T|   F|     F|        T|  T|          F||F
         F|   F|     F|        T|  T|          F||F
         T|   T|     T|        F|  T|          F||F
         F|   T|     T|        F|  T|          F||F
         T|   F|     T|        F|  T|          F||F
         F|   F|     T|        F|  T|          F||F
         T|   T|     F|        F|  T|          F||F
         F|   T|     F|        F|  T|          F||F
         T|   F|     F|        F|  T|          F||F
         F|   F|     F|        F|  T|          F||F
         T|   T|     T|        T|  F|          F||F
         F|   T|     T|        T|  F|          F||F
         T|   F|     T|        T|  F|          F||F
         F|   F|     T|        T|  F|          F||F
         T|   T|     F|        T|  F|          F||F
         F|   T|     F|        T|  F|          F||F
         T|   F|     F|        T|  F|          F||F
         F|   F|     F|        T|  F|          F||F
         T|   T|     T|        F|  F|          F||F
         F|   T|     T|        F|  F|          F||F
         T|   F|     T|        F|  F|          F||F
         F|   F|     T|        F|  F|          F||F
         T|   T|     F|        F|  F|          F||F
         F|   T|     F|        F|  F|          F||F
         T|   F|     F|        F|  F|          F||F
         F|   F|     F|        F|  F|          F||F
(interpreter and (one and (lookahead and (simple and (not slow and state_mach)))))
	interpreter = T
 and
		one = T
	 and
			lookahead = T
		 and
				simple = T
			 and
					slow = F
				 and
					state_mach = T

Note: The simplifier is of O(n+1)! asymtotic complexity (due to a bug, it really should be
O(n!)) where n is the number of words in the expression, so it really is incredibly
inefficient, and really cannot handle more than 7 variables, although 8 works if you
are patient (several minutes).
*)
datatype BinOp = AND | OR | BI_IMP | RI_IMP | LF_IMP
datatype BoolOp = BINOP of (BinOp*BoolOp*BoolOp)
				| NOT of (BoolOp)
				| INPUT of (string)
				| LIT of bool
				| VALUE of Expr
and
 Expr =
	SIMPLIFY of Expr
	|REGULAR of BoolOp

datatype Effect =
	PRINT_TABLE	of Expr
	|PRINT_TREE	of Expr
	|PRINT_BOOLOP of Expr

exception KeyError

fun findval symb nil = raise KeyError
	| findval symb ((thisSymb,value)::t) =
		if thisSymb = symb
		then value
		else findval symb t

fun evaluate (INPUT(c)) data = findval c data
	| evaluate (BINOP(BOp,op1,op2)) data =
		let val V1 = (evaluate op1 data)
			val V2 = (evaluate op2 data)
		in
			case BOp of
			AND => V1 andalso V2
			|OR => V1 orelse V2
			|BI_IMP => (V1 = V2)
			|RI_IMP => not V1 orelse V2
			|LF_IMP => V1 orelse not V2
		end
	| evaluate (NOT(operation)) data =
		not (evaluate operation data)
	| evaluate (LIT(BVal)) data = BVal

(*
This creates the tokenizer
*)
local
	fun InsertWhiteSpace nil = []
		| InsertWhiteSpace (CurChar::L) =
			if CurChar = #")" orelse CurChar = #"("	orelse CurChar = #"="
			then (#" ")::(CurChar::((#" ")::(InsertWhiteSpace L)))
			else CurChar::(InsertWhiteSpace L)
	(*removes extra whitespace and does most of the work of tokenizing*)
	fun GetWord [] = ([],[])
		| GetWord (Ch::L) =
			if Ch = #" " orelse Ch = #"\n"
			then ([],L)
			else let val (Word,RestStr) = GetWord L
				 in  (Ch::Word,RestStr)
				 end

	fun Split_helper nil = []
		| Split_helper L =
				let val (Word,Rest) = GetWord L
				in (String.implode Word)::(Split_helper Rest)
				end

	fun RevEmpty nil = []
		|RevEmpty (""::T) = RevEmpty T
		| RevEmpty (H::T) = H::(RevEmpty T)

	fun Split S = Split_helper(InsertWhiteSpace (String.explode S))
in
	fun Tokenize Str = RevEmpty(Split(Str))
end
(*
Convert helpers
*)
local
	val GetImport = fn
		"(" => 100
		|"or" => 4
		|"and" => 3
		|"not" => 1
		|"if" => 7
		|"then" => 8
		|"unless" => 6
		|")" => 1200
		|word => 10(*this value should not affect anything*)

	val IsBinOp = fn
		"and" => true
		|"or" => true
		|"unless" => true
		|"if" => true
		|other => false

	val IsUniOp = fn
		"not" => true
		|"then" => true
		|other => false

	val IsDoubleUniOp = fn
		"if" => true
		|other => false

	fun MakeBinTree Left Right Binop =
		BINOP(
		(case Binop of
		"and" => AND
		| "or" => OR
		| "unless" => BI_IMP
		|"if" => LF_IMP)
		,Left,Right)

	fun MakeUnTree PrevTree UnOp =
		case UnOp of
		"not" => NOT(PrevTree)
		|"then" => PrevTree

	fun MakeDoubleUnTree First Second DoubleUnOp =
		case DoubleUnOp of
		"if" => BINOP(RI_IMP,First,Second)

	exception BadWord
	exception EmptyStr

	fun eat Word (S::L) =
		if S = Word
		then L
		else (print("expected: " ^ Word ^ "\ngot: " ^ S); raise BadWord)

	fun IsValue [] Word = false
		|IsValue ((Val,_)::L) Word = (Val = Word) orelse (IsValue L Word)

	fun GetValue [] Word = raise BadWord
		|GetValue ((Val,Conv)::L) Word =
			if (Val = Word)
			then Conv
			else GetValue L Word

	fun ConvertWord Values Word =
		case Word of
			"True" => LIT(true)
			|"False" => LIT(false)
			|Symb =>
				if (IsValue Values Symb)
				then VALUE(GetValue Values Symb)
				else INPUT(Symb)

	fun ConvertUnary Values (Word::Rest) Import =
	if Word = "(" orelse IsUniOp(Word) orelse IsDoubleUniOp(Word)
		then
			let val (Tree,NewRest) = ConvertPartialBoolean Values Rest (GetImport Word)
			in
				if Word = "("
					then (Tree,eat ")" NewRest)
				else if IsDoubleUniOp(Word)
					then
						let val (RightTree,FinalRest) = ConvertPartialBoolean Values NewRest (GetImport "(") (*there is no way to change the way this is parsed with values*)
						in (MakeDoubleUnTree Tree RightTree Word, FinalRest)
						end
				else ((MakeUnTree Tree Word),NewRest)
			end
	else (*we know that Word is a variable now*)
		if (length Rest) > 0 andalso (IsBinOp (hd Rest)) andalso Import > (GetImport (hd Rest))
		then ConvertBinary Values Rest (GetImport (hd Rest)) (ConvertWord Values Word)
		else ((ConvertWord Values Word),Rest)

	and
	ConvertBinary Values SList Import LeftTree =
		if (length SList) > 0 andalso (IsBinOp (hd SList)) andalso Import >= (GetImport (hd SList))
		then
			let val binop = hd(SList)
				val (RightTree,NewRest) = ConvertUnary Values (tl SList) (GetImport binop)
				val ThisTree = MakeBinTree LeftTree RightTree binop
			in ConvertBinary Values NewRest (GetImport binop) ThisTree
			end
		else (LeftTree,SList)

	and
	ConvertPartialBoolean Values SList Import =
		let val (LeftTree,Rest) = ConvertUnary Values SList Import
		in ConvertBinary Values Rest Import LeftTree
		end

	and
	ConvertBooleans Values SList = ConvertPartialBoolean Values SList 10000

	and
	ConvertSimplify Values (Word::Rest) =
		let val IsSimp = (Word = "simplify")
			val SRest = if IsSimp then Rest else (Word::Rest)
			val (Conv,NewRest) = ConvertBooleans Values SRest
		in
			if IsSimp
			then (SIMPLIFY(REGULAR(Conv)),NewRest)
			else (REGULAR(Conv),NewRest)
		end

	and
	ConvExprs Values [] = []
	|ConvExprs Values (Word::Rest) =
		if Word = "val"
		then
			let val (ValKey::EqualRest) = Rest
				val SimpleRest = eat "=" EqualRest
				val (Exps,NewRest) = (ConvertSimplify Values SimpleRest)
			in (ConvExprs ((ValKey,Exps)::Values) NewRest)
			end
		else
			let val (Exps,NewRest) = (ConvertSimplify Values Rest)
			in
			(
				case Word of
				"print_tree" => (PRINT_TREE(Exps))
				|"print_table" => (PRINT_TABLE(Exps))
				|"print_value" => (PRINT_BOOLOP(Exps))
				|OtherSymb => (print("Error, expected expression got: " ^ OtherSymb); raise BadWord)
			)::(ConvExprs Values NewRest)
			end
in
	val convert = ConvExprs
end
(*
This section allows for the readable printing of the parsed truth tree
*)
val BinOpToString = fn
	AND => "and"
	|OR => "or"
	|BI_IMP => "unless"
	|LF_IMP => "if"
	|RI_IMP => "only if"

fun BoolToStr true = "T"
	|BoolToStr false = "F"
local
	fun MultTab 0 = ""
		|MultTab Tab = "\t" ^ (MultTab (Tab-1))

	fun PrintTT Tab Bool Conv =
		case Conv of
		NOT(Term) => (PrintTT Tab (not Bool) Term)
		|INPUT(Word) => (MultTab Tab) ^ Word ^ " = " ^ (BoolToStr Bool) ^ "\n"
		|LIT(Val) => (MultTab Tab) ^ (BoolToStr Val) ^ "\n"
		|BINOP(BOp,Left,Right) =>
			(PrintTT (Tab+1) Bool Left) ^ (MultTab Tab)
			^ " " ^ (BinOpToString BOp) ^ " \n"
			^ (PrintTT (Tab+1) Bool Right)
in
	val PrintTruthTree = PrintTT 0 true
end
(*
All of this nonsense is to help the truth table print properly and simplifiys the expression
*)
local
	fun PrintSpace 0 = ""
		|PrintSpace Num = " " ^ (PrintSpace (Num-1))

	fun IsInList [] Name = false
		|IsInList (TName::OtherNames) Name = ((TName = Name) orelse (IsInList OtherNames Name))

	fun GetNames CurList Conv =
		case Conv of
		(INPUT(Word)) =>
			if not(IsInList CurList Word)
			then Word::CurList
			else CurList
		| NOT(Info) => GetNames CurList Info
		| BINOP(_,RInfo,LInfo) => GetNames (GetNames CurList RInfo) LInfo
		| LIT(Val) => CurList

	fun TruthTNamesToStr nil = ""
		|TruthTNamesToStr (ThisName::Names) = (TruthTNamesToStr Names) ^ ThisName ^ "|"

	fun PrintTruthTInputData nil = "|"
		|PrintTruthTInputData ((ThisName,Bool)::NamePairs) =
			(PrintSpace ((size ThisName) - 1)) ^
			(BoolToStr(Bool)) ^ "|" ^ (PrintTruthTInputData NamePairs)

	fun PrintTruthTLine Conv NamePairs =
		(PrintTruthTInputData NamePairs) ^
		(BoolToStr (evaluate Conv NamePairs))

	fun PrintTruthTDataOutput Conv nil FinalPairs =
			(PrintTruthTLine Conv FinalPairs) ^ "\n"
		|PrintTruthTDataOutput Conv (ThisName::Names) CurPairs =
			(PrintTruthTDataOutput Conv Names ((ThisName,true)::CurPairs)) ^
			(PrintTruthTDataOutput Conv Names ((ThisName,false)::CurPairs))

	fun PrintExps Conv =
		case Conv of
		NOT(X) => "not " ^ (PrintExps X)
		| INPUT(Word) => Word
		| LIT(true) => "True"
		| LIT(false) => "False"
		| BINOP(BOp,X,Y) => "(" ^ (PrintExps X) ^ " " ^ (BinOpToString BOp) ^ " " ^ (PrintExps Y) ^ ")"

	fun append_to_all W nil = []
		|append_to_all W (L::AccumList) = (W::L)::(append_to_all W AccumList)
	fun add_to_all W nil = []
		|add_to_all W (L::AccumList) = (W @ L)::(add_to_all W AccumList)
	local
		fun is_in N [] = false
			|is_in N (W::L) = if W = N then true else is_in N L

		fun partials 0 [] = [[]]
			|partials n [] = [[]]
			|partials n (H::L) =
			(if (length L) >= n
			then partials n L
			else []) @
			(append_to_all H (partials (n-1) L))
		fun get_rest All Some = List.filter (fn x => not (is_in x Some)) All
		fun pair_up All nil = []
			|pair_up All (L::LL) =
				if L = All
				then pair_up All LL
				else (L,get_rest All L)::(pair_up All LL)
	in
		(*this gets all the ways to group up the list into two parts*)
		fun get_all_pairs L = pair_up L (partials 1 L)
	end

	(*Equals is a symbolic comparison, not a truth table comparsion, but for the purposes of Simplify this is the same thing*)
	fun Equals (BINOP(BOp,X,Y)) (BINOP(BOp1,X1,Y1)) =
			BOp = BOp1 andalso
			(Equals X X1 orelse Equals X Y1) andalso
			(Equals Y X1 orelse Equals Y Y1)
		|Equals (NOT(X)) (NOT(Y)) = Equals X Y
		|Equals (INPUT(W1)) (INPUT(W2)) = (W1 = W2)
		|Equals (LIT(V1)) (LIT(V2)) = (V1 = V2)
		|Equals _ _ = false

	fun ElimBNots Conv =
		case Conv of
		NOT(LIT(Lit)) => LIT(not Lit)
		|NOT(NOT(X)) => ElimBNots X (*Also performs a double negation elimination as it goes*)
		|NOT(BINOP(BOp,X,Y)) =>
			(case BOp of
			OR => BINOP(AND,(ElimBNots (NOT X)),(ElimBNots (NOT Y)))
			|AND => BINOP(OR,(ElimBNots (NOT X)),(ElimBNots (NOT Y)))
			|BI_IMP => BINOP(BI_IMP,(ElimBNots (NOT X)),(ElimBNots (NOT Y)))
			|RI_IMP => BINOP(AND,(ElimBNots X),(ElimBNots (NOT Y)))
			|LF_IMP => BINOP(AND,(ElimBNots (NOT X)),(ElimBNots Y)))
		|NOT(Small) => NOT(ElimBNots Small)
		|BINOP(BOp,X,Y) => BINOP(BOp,ElimBNots X,ElimBNots Y)
		|Word => Word

	fun CountTerms Conv =
		case Conv of
		BINOP(_,X,Y) => 2 + (CountTerms X) + (CountTerms Y)
		|NOT(X) => (CountTerms X)
		|Word => 0

	fun generate_help CurL Names =
		case Names of
		nil => [CurL]
		|(N::NL) => (generate_help ((N,true)::CurL) NL) @ (generate_help ((N,false)::CurL) NL)

	fun generate_NV_pairs Names = generate_help nil Names
	fun create_single Conv NPComb N =
		let val ValT = (evaluate Conv ((N,true)::NPComb))
			val ValF = (evaluate Conv ((N,false)::NPComb))
		in
			if ValT = ValF
				then LIT(ValT)
			else if ValT = true andalso ValF = false
				then INPUT(N)
			else(*if ValT = false andalso ValF = true*)
				NOT(INPUT(N))
		end
	exception EmptyListError
	exception ImperfectMatch
	val NULLCONV = INPUT("()")
	fun compare_TF (Conv::nil) = [Conv]
		|compare_TF (Conv::RestConvs) =
			let val Convs = compare_TF RestConvs
				val CSize = length Convs
			in
				case CSize of
				1 => if hd(Convs) = Conv
					 then Convs
					 else Conv::Convs
				|2 => if hd(Convs) = Conv orelse hd(tl(Convs)) = Conv
					 then Convs
					 else raise ImperfectMatch
			end

	fun apply_tts Conv CurNPComb NL =
		case (length NL) of
		0 => LIT(evaluate Conv [])(*it should only have no variables when the function has none*)
		| 1 => create_single Conv CurNPComb (hd NL)
		| _ => apply_to_all Conv CurNPComb (get_all_pairs NL)
	and
	apply_to Conv CurNPComb (Left,Right) =
		if length Left > 1 andalso length Right > 1
		then
		let	val RightNPCombs = add_to_all CurNPComb (generate_NV_pairs Left)(*note that these are switched!*)
			val LeftNPCombs = add_to_all CurNPComb (generate_NV_pairs Right)
			val RConvs = compare_TF (make_all_combs Conv RightNPCombs Right)
			val LConvs = compare_TF (make_all_combs Conv LeftNPCombs Left)
		in
			case RConvs of
			[RConv] => RConv(*if there is no difference between left being true or false then it is just the right*)
			|[RConv1,RConv2] =>
				case LConvs of
				[LConv] => LConv
				|[LConv1,LConv2] =>
					if 		(RConv1 = LIT(true) orelse RConv2 = LIT(true))
					andalso (LConv1 = LIT(true) orelse LConv2 = LIT(true))
						then BINOP(OR,
							(if RConv1 = LIT(true) then RConv2 else RConv1),
							(if LConv1 = LIT(true) then LConv2 else LConv1))
					else if (RConv1 = LIT(false) orelse RConv2 = LIT(false))
					andalso (LConv1 = LIT(false) orelse LConv2 = LIT(false))
						then BINOP(AND,
							(if RConv1 = LIT(false) then RConv2 else RConv1),
							(if LConv1 = LIT(false) then LConv2 else LConv1))
					else if ((ElimBNots (NOT(RConv1))) = (ElimBNots RConv2))
					andalso ((ElimBNots (NOT(LConv1))) = (ElimBNots LConv2))
						then BINOP(BI_IMP,RConv2,LConv2)
					else
						(print("EEEKE!\n");	raise ImperfectMatch)
		end
		else
			let val Single = if length Right = 1 then Right else Left
				val Group = if length Right = 1 then Left else Right
				val N = hd(Single)
				val ValT = apply_tts Conv ((N,true)::CurNPComb) Group
				val ValF = apply_tts Conv ((N,false)::CurNPComb) Group
			in
				if ValT = ValF
					then ValT
				else if ValT = LIT(true) andalso ValF = LIT(false)
					then INPUT(N)
				else if ValT = LIT(false) andalso ValF = LIT(true)
					then NOT(INPUT(N))
				else if ValF = LIT(true)
					then BINOP(OR,NOT(INPUT(N)),ValT)
				else if ValF = LIT(false)
					then BINOP(AND,INPUT(N),ValT)
				else if ValT = LIT(true)
					then BINOP(OR,INPUT(N),ValF)
				else if ValT = LIT(false)
					then BINOP(AND,NOT(INPUT(N)),ValF)
				else if ValT = LIT(false)
					then BINOP(AND,NOT(INPUT(N)),ValF)
				else if (ElimBNots (NOT(ValF))) = (ElimBNots ValT)
					then BINOP(BI_IMP,INPUT(N),ValT)
				else
					BINOP(OR,BINOP(AND,INPUT(N),ValT),BINOP(AND,NOT(INPUT(N)),ValF))
			end
	and
	make_all_combs Conv AllCombs NL =
		case AllCombs of
		nil => nil
		| (Comb::NPCombs) => (apply_tts Conv Comb NL)::(make_all_combs Conv NPCombs NL)
	and
	apply_all_help Conv CurNPComb Pairs BestSize BestConv =
		case Pairs of
		nil => BestConv
		|(pair::RestPairs) =>
			let val Applied = apply_to Conv CurNPComb pair
					handle
					ImperfectMatch => NULLCONV
				val ThisSize = CountTerms Applied
			in
				if ThisSize < BestSize andalso not(Applied = NULLCONV)
					then apply_all_help Conv CurNPComb RestPairs ThisSize Applied
				else
					apply_all_help Conv CurNPComb RestPairs BestSize BestConv
			end
	and
	apply_to_all Conv CurNPComb Pairs = apply_all_help Conv CurNPComb Pairs 100000000 (LIT(true))

in
	fun PrintTruthTable Conv =
		let	val Names = GetNames nil Conv
		in
			(TruthTNamesToStr Names) ^ "|" ^ (PrintExps Conv) ^ "\n" ^
			(PrintTruthTDataOutput Conv Names nil)
		end
	fun Simplify Conv =
		let val SimpleConv = apply_tts Conv nil (GetNames nil Conv)
		in
			if CountTerms Conv > CountTerms SimpleConv
			then SimpleConv
			else Conv
		end
	fun print_expression Conv = (PrintExps Conv) ^ "\n"
end
fun SubstituteValues Conv =
	case Conv of
	BINOP(BOp,X,Y) => BINOP(BOp,SubstituteValues X,SubstituteValues Y)
	|NOT(X) => NOT(SubstituteValues X)
	|VALUE(Express) => EvalSimp Express
	|LitOrInp => LitOrInp

and
 EvalSimp Express =
	case Express of
	SIMPLIFY(REGULAR(Conv)) => (Simplify (SubstituteValues Conv))
	|REGULAR(Conv) => (SubstituteValues Conv)

fun EvalEffect nil = ()
	|EvalEffect (Eff::EffList) =
	(
		print(
			case Eff of
			PRINT_BOOLOP(Simp) => print_expression (EvalSimp Simp)
			|PRINT_TABLE(Simp) => PrintTruthTable (EvalSimp Simp)
			|PRINT_TREE(Simp) => PrintTruthTree (EvalSimp Simp)
		);
		EvalEffect(EffList)
	)


(*****************             *
 ***************** FILE READER *
 *****************             *)

fun read filename = TextIO.input (TextIO.openIn filename)

fun boolean_eval filename =
let
  val src = read filename
  val tokens = Tokenize src
  val ExprList = convert [] tokens
in
  (EvalEffect ExprList)
end

val _ = boolean_eval "test.bool"
