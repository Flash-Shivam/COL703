open Formula;;
module BDD = struct
		type sat_assignment = string list

		(* define the type robdd in whatever way you want  *)
		type robdd = bool list ;;

		exception Not_implemented


		let bddFromExpr bexpr order = raise Not_implemented;;


		let sat_count bdd = raise Not_implemented ;;
		let all_sat bdd = raise Not_implemented ;;
		let any_sat bdd =  raise Not_implemented ;;


		let to_dot bdd = raise Not_implemented;;

end  ;;

(* let a = (Program.Constant true);;
a;; *)
exception Cant_be_evaluated
exception No_valid_assingment
let rec feval bexpr bassign = match bexpr with
| Program.Constant(false) -> 0
| Program.OprUnary(Program.NOT,a) -> if ((feval a bassign) =1) then 0 else 1
| Program.Variable(x) -> if (List.mem x bassign) then 1 else raise Cant_be_evaluated
| Program.Constant(true) -> 1
| Program.OprBinary(Program.AND,a,b) -> if ( (feval a bassign) = 0 || (feval b bassign) = 0) then 0 else (feval a bassign) * (feval b bassign)
| Program.OprBinary(Program.OR,a,b) -> if ( (feval a bassign) = 1 || (feval b bassign) = 1) then 1 else 0;
| Program.OprBinary(Program.IFTHEN,a,b) -> if((feval a bassign) = 0 || (feval b bassign) = 1) then 1 else 0
| Program.OprBinary(Program.IFF,a,b) -> if((feval a bassign) = (feval b bassign)) then 1 else 0
| Program.OprTernary(Program.IFTHENELSE,a,b,c) -> if((feval a bassign) = 1) then (feval b bassign) else (feval c bassign)
;;

let safe_fval bexpr = try feval bexpr ([]) with Cant_be_evaluated -> -1;;

let rec substitute_x bexpr var_x bool_x = match bexpr with
| Program.Variable(x) -> if (x = var_x) then (if bool_x then Program.Constant(true) else Program.Constant(false)) else Program.Variable(x)
| Program.OprUnary(Program.NOT,a) -> Program.OprUnary(Program.NOT,substitute_x a var_x bool_x)
| Program.OprBinary(z,a,b) -> Program.OprBinary(z,substitute_x a var_x bool_x,substitute_x b var_x bool_x)
| Program.OprTernary(Program.IFTHENELSE,a,b,c) -> Program.OprTernary(Program.IFTHENELSE,substitute_x a var_x bool_x,substitute_x b var_x bool_x,substitute_x c var_x bool_x)
| z -> z;;


let rec conv_ifte bexpr = match bexpr with
| Program.OprUnary(Program.NOT,a) -> Program.OprTernary(Program.IFTHENELSE,(conv_ifte a),Program.Constant(false),Program.Constant(true))
| Program.OprBinary(Program.AND,a,b) -> Program.OprTernary(Program.IFTHENELSE,(conv_ifte a),(conv_ifte b),Program.Constant(false))
| Program.OprBinary(Program.OR,a,b) -> Program.OprTernary(Program.IFTHENELSE,(conv_ifte a),Program.Constant(true),(conv_ifte b))
| Program.OprBinary(Program.IFTHEN,a,b) -> Program.OprTernary(Program.IFTHENELSE,(conv_ifte a),(conv_ifte b),Program.Constant(true))
| Program.OprBinary(Program.IFF,a,b) -> Program.OprTernary(Program.IFTHENELSE,(conv_ifte a),(conv_ifte b),(conv_ifte (Program.OprUnary(Program.NOT,b))))
| Program.OprTernary(Program.IFTHENELSE,a,b,c) -> Program.OprTernary(Program.IFTHENELSE,(conv_ifte a),(conv_ifte b),(conv_ifte c))
| a -> a
;;


let table = Hashtbl.create 1000;;
let table2 = Hashtbl.create 1000;;
let var_table = Hashtbl.create 1000;;




let mk index low high = if (low = high) then low else if (Hashtbl.mem table2 (index,low,high)) then Hashtbl.find table2 (index,low,high) else let p = Hashtbl.length table in let z = Hashtbl.add table (p) (index,low,high) in let y = Hashtbl.add table2 (index,low,high) (p) in (p);;


let rec robddFromExpr bexpr order num index = if (index > num) then safe_fval bexpr else match order with
| head :: tail -> (mk index (robddFromExpr (substitute_x (bexpr) (head) (false)) tail num (index+1)) (robddFromExpr (substitute_x (bexpr) (head) (true)) tail num (index+1)));;

let rec power x n = if n = 0 then 1 else if n = 1 then x else x * (power x (n-1));;

let get_low node = match (Hashtbl.find table node) with
| (a,b,c) -> b;;

let get_high node = match (Hashtbl.find table node) with
| (a,b,c) -> c;;

let get_var node = match (Hashtbl.find table node) with
| (a,b,c) -> a;;

let rec count_sat node = if (node = 0) then 0 else if (node = 1) then 1 else (power (2) (get_var (get_low node) - (get_var node) -1 ))*(count_sat (get_low node)) + (power (2) (get_var (get_high node) - (get_var node) -1 )  )*(count_sat (get_high node));;


let f_count node = (power (2) ((get_var node)-1)) * (count_sat node);;


let rec fill_var_table order num = match order with
| [x] -> Hashtbl.add var_table (num) (x)
| head :: tail -> let p = Hashtbl.add var_table (num) (head) in fill_var_table tail (num + 1);;

let f_robdd bexpr order = let f = Hashtbl.clear var_table in let v = fill_var_table order (1) in let r = Hashtbl.clear table in let t = Hashtbl.clear table2 in let m = Hashtbl.add table (0) (List.length order+1,-1,-1) in let n = Hashtbl.add table (1) (List.length order+1,-1,-1) in robddFromExpr bexpr order (List.length order) (1);;

let rec f_any_sat node list_l = if node = 0 then raise No_valid_assingment else if node = 1 then list_l else if ((get_low node) = 0) then f_any_sat (get_high node) (list_l@[(Hashtbl.find var_table (get_var node))]) else  f_any_sat (get_low node) (list_l);;

let f_sat node = f_any_sat node ([]);;
