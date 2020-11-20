module Program = struct
	type bool_opr = AND
                | OR
                | NOT
                | IFTHEN
                | IFF
                | IFTHENELSE

    type bool_expr = OprUnary of bool_opr * bool_expr
                                | OprBinary of bool_opr * bool_expr * bool_expr
                                | OprTernary of bool_opr * bool_expr * bool_expr * bool_expr
                                | Variable of string
                                | Constant of bool
end;;
