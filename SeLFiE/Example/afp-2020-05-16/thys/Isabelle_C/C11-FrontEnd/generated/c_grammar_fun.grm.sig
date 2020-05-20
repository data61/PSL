structure C_Grammar_Rule = 
struct
(*#line 1.2 "c_grammar_fun.grm"*)open C_Ast open C_Grammar_Rule_Lib

type start_happy = (CTranslUnit, (CExtDecl, (CStat, (CExpr, unit) either) either) either) either

fun start_happy4 (x : start_happy) = case x of Right (Right (Right (Left x))) => SOME x | _ => NONE
fun start_happy3 (x : start_happy) = case x of Right (Right (Left x)) => SOME x | _ => NONE
fun start_happy2 (x : start_happy) = case x of Right (Left x) => SOME x | _ => NONE
fun start_happy1 (x : start_happy) = case x of Left x => SOME x | _ => NONE


(*#line 8775.1 "c_grammar_fun.grm.sml"*)
datatype svalue0 = VOID | ntVOID of unit | clangcversion of  (C_Ast.ClangCVersion) | x5f_x5f_builtin_types_compatible_p of  (string) | x5f_x5f_builtin_offsetof of  (string) | x5f_x5f_builtin_va_arg of  (string) | x5f_x5f_imag_x5f_x5f of  (string) | x5f_x5f_real_x5f_x5f of  (string) | x5f_x5f_extension_x5f_x5f of  (string) | x5f_x5f_attribute_x5f_x5f of  (string) | tyident of  (C_Ast.ident) | ident of  (C_Ast.ident) | cstr of  (C_Ast.cString) | cfloat of  (C_Ast.cFloat) | cint of  (C_Ast.cInteger) | cchar of  (C_Ast.cChar) | while0 of  (string) | volatile of  (string) | void of  (string) | unsigned of  (string) | union of  (string) | x5f_x5f_thread of  (string) | typeof of  (string) | typedef of  (string) | switch of  (string) | struct0 of  (string) | x5f_Static_assert of  (string) | static of  (string) | sizeof of  (string) | signed of  (string) | short of  (string) | return0 of  (string) | restrict of  (string) | register of  (string) | x5f_Nonnull of  (string) | x5f_Nullable of  (string) | x5f_Noreturn of  (string) | x5f_x5f_label_x5f_x5f of  (string) | long of  (string) | x5f_x5f_int_x31_x32_x38 of  (string) | int of  (string) | inline of  (string) | if0 of  (string) | goto of  (string) | x5f_Generic of  (string) | for0 of  (string) | float of  (string) | extern of  (string) | enum of  (string) | else0 of  (string) | double of  (string) | do0 of  (string) | default of  (string) | x5f_Complex of  (string) | continue of  (string) | const of  (string) | char of  (string) | case0 of  (string) | x5f_Bool of  (string) | break of  (string) | auto of  (string) | asm of  (string) | x5f_Atomic of  (string) | alignas of  (string) | alignof of  (string) | x2e_x2e_x2e of  (string) | x7d of  (string) | x7b of  (string) | x3b of  (string) | x2c of  (string) | x3e_x3e_x3d of  (string) | x3c_x3c_x3d of  (string) | x7c_x3d of  (string) | x5e_x3d of  (string) | x26_x3d of  (string) | x25_x3d of  (string) | x2f_x3d of  (string) | x2a_x3d of  (string) | x2d_x3d of  (string) | x2b_x3d of  (string) | x3d of  (string) | x3a of  (string) | x3f of  (string) | x7c_x7c of  (string) | x26_x26 of  (string) | x7c of  (string) | x5e of  (string) | x21_x3d of  (string) | x3d_x3d of  (string) | x3e_x3d of  (string) | x3e of  (string) | x3c_x3d of  (string) | x3c of  (string) | x3e_x3e of  (string) | x3c_x3c of  (string) | x26 of  (string) | x25 of  (string) | x2f of  (string) | x2a of  (string) | x2d of  (string) | x2b of  (string) | x2d_x2d of  (string) | x2b_x2b of  (string) | x7e of  (string) | x21 of  (string) | x2e of  (string) | x2d_x3e of  (string) | x5d of  (string) | x5b of  (string) | x29 of  (string) | x28 of  (string) | attribute_params of  ( ( CExpr list )  Reversed) | attribute of  (CAttr Maybe) | attribute_list of  ( ( CAttr list )  Reversed) | attr of  (CAttr list) | attrs of  (CAttr list) | attrs_opt of  (CAttr list) | identifier of  (Ident) | clang_version_literal of  (ClangCVersion) | string_literal_list of  ( ( CString list )  Reversed) | string_literal of  (CStrLit) | constant of  (CConst) | constant_expression of  (CExpr) | assignment_expression_opt of  (CExpr Maybe) | expression_opt of  (CExpr Maybe) | comma_expression of  ( ( CExpr list )  Reversed) | expression of  (CExpr) | assignment_operator of  (CAssignOp Located) | assignment_expression of  (CExpr) | conditional_expression of  (CExpr) | logical_or_expression of  (CExpr) | logical_and_expression of  (CExpr) | inclusive_or_expression of  (CExpr) | exclusive_or_expression of  (CExpr) | and_expression of  (CExpr) | equality_expression of  (CExpr) | relational_expression of  (CExpr) | shift_expression of  (CExpr) | additive_expression of  (CExpr) | multiplicative_expression of  (CExpr) | cast_expression of  (CExpr) | unary_operator of  (CUnaryOp Located) | unary_expression of  (CExpr) | argument_expression_list of  ( ( CExpr list )  Reversed) | postfix_expression of  (CExpr) | offsetof_member_designator of  ( ( CDesignator list )  Reversed) | generic_assoc of  ( ( CDecl Maybe * CExpr ) ) | generic_assoc_list of  ( ( ((CDecl Maybe * CExpr)) list )  Reversed) | primary_expression of  (CExpr) | array_designator of  (CDesignator) | designator of  (CDesignator) | designator_list of  ( ( CDesignator list )  Reversed) | designation of  (CDesignator list) | initializer_list of  (CInitList Reversed) | initializer_opt of  (CInit Maybe) | initializer of  (CInit) | postfix_abstract_declarator of  (CDeclrR) | unary_abstract_declarator of  (CDeclrR) | postfix_array_abstract_declarator of  ( ( CDeclrR -> CDeclrR ) ) | array_abstract_declarator of  ( ( CDeclrR -> CDeclrR ) ) | postfixing_abstract_declarator of  ( ( CDeclrR -> CDeclrR ) ) | abstract_declarator of  (CDeclrR) | type_name of  (CDecl) | identifier_list of  ( ( Ident list )  Reversed) | parameter_declaration of  (CDecl) | parameter_list of  ( ( CDecl list )  Reversed) | parameter_type_list of  ( ( CDecl list * Bool ) ) | postfix_old_function_declarator of  (CDeclrR) | old_function_declarator of  (CDeclrR) | function_declarator_old of  (CDeclr) | paren_identifier_declarator of  (CDeclrR) | postfix_identifier_declarator of  (CDeclrR) | unary_identifier_declarator of  (CDeclrR) | identifier_declarator of  (CDeclrR) | simple_paren_typedef_declarator of  (CDeclrR) | paren_postfix_typedef_declarator of  (CDeclrR) | paren_typedef_declarator of  (CDeclrR) | clean_postfix_typedef_declarator of  (CDeclrR) | clean_typedef_declarator of  (CDeclrR) | parameter_typedef_declarator of  (CDeclrR) | typedef_declarator of  (CDeclrR) | asm_opt of  (CStrLit Maybe) | declarator of  (CDeclrR) | type_qualifier_list of  ( ( CTypeQual list )  Reversed) | type_qualifier of  (CTypeQual) | enumerator of  ( ( Ident * CExpr Maybe ) ) | enumerator_list of  ( ( ((Ident * CExpr Maybe)) list )  Reversed) | enum_specifier of  (CEnum) | struct_identifier_declarator of  ( ( CDeclr Maybe * CExpr Maybe ) ) | struct_declarator of  ( ( CDeclr Maybe * CExpr Maybe ) ) | struct_declaring_list of  (CDecl) | struct_default_declaring_list of  (CDecl) | struct_declaration of  (CDecl) | struct_declaration_list of  ( ( CDecl list )  Reversed) | struct_or_union of  (CStructTag Located) | struct_or_union_specifier of  (CStructUnion) | elaborated_type_name of  (CTypeSpec) | typedef_type_specifier of  ( ( CDeclSpec list )  Reversed) | typedef_declaration_specifier of  ( ( CDeclSpec list )  Reversed) | sue_type_specifier of  ( ( CDeclSpec list )  Reversed) | sue_declaration_specifier of  ( ( CDeclSpec list )  Reversed) | basic_type_specifier of  ( ( CDeclSpec list )  Reversed) | basic_declaration_specifier of  ( ( CDeclSpec list )  Reversed) | basic_type_name of  (CTypeSpec) | type_specifier of  (CDeclSpec list) | alignment_specifier of  (CAlignSpec) | function_specifier of  (CFunSpec) | storage_class of  (CStorageSpec) | declaration_qualifier_without_types of  (CDeclSpec) | declaration_qualifier of  (CDeclSpec) | declaration_qualifier_list of  ( ( CDeclSpec list )  Reversed) | declaration_specifier of  (CDeclSpec list) | declaring_list of  (CDecl) | asm_attrs_opt of  ( ( CStrLit Maybe * CAttr list ) ) | default_declaring_list of  (CDecl) | declaration_list of  ( ( CDecl list )  Reversed) | declaration of  (CDecl) | asm_clobbers of  ( ( CStrLit list )  Reversed) | asm_operand of  (CAsmOperand) | nonnull_asm_operands of  ( ( CAsmOperand list )  Reversed) | asm_operands of  (CAsmOperand list) | maybe_type_qualifier of  (CTypeQual Maybe) | asm_statement of  (CAsmStmt) | jump_statement of  (CStat) | iteration_statement of  (CStat) | selection_statement of  (CStat) | expression_statement of  (CStat) | label_declarations of  ( ( Ident list )  Reversed) | nested_function_definition of  (CFunDef) | nested_declaration of  (CBlockItem) | block_item of  (CBlockItem) | block_item_list of  ( ( CBlockItem list )  Reversed) | leave_scope of  (unit) | enter_scope of  (unit) | compound_statement of  (CStat) | labeled_statement of  (CStat) | statement of  (CStat) | function_declarator of  (CDeclr) | function_definition of  (CFunDef) | external_declaration of  (CExtDecl) | ext_decl_list of  ( ( CExtDecl list )  Reversed) | translation_unit of  (CTranslUnit) | start_happy of  ( ( CTranslUnit, (CExtDecl, (CStat, (CExpr, unit) either) either) either )  either)
fun find_list msg mk_name l =
  let val tab =
        fold (fn (name, occ) =>
               fold (fn name => fn (tab, nb) => (Inttab.update (nb, name) tab, nb + 1))
                    (if occ = 1 then [name]
                                else map_range (mk_name name) occ))
             l
             (Inttab.empty, 0)
        |> #1
  in
    fn i => case Inttab.lookup tab i of NONE => error msg | SOME name => name
  end
val type_reduce = find_list "reduce type not found" K [
  (" ( ( CTranslUnit, (CExtDecl, (CStat, (CExpr, unit) either) either) either )  either)", 4),
  (" (CTranslUnit)", 1),
  (" ( ( CExtDecl list )  Reversed)", 3),
  (" (CExtDecl)", 4),
  (" (CFunDef)", 14),
  (" (CDeclr)", 1),
  (" (CStat)", 7),
  (" (CStat)", 4),
  (" (CStat)", 2),
  (" (unit)", 1),
  (" (unit)", 1),
  (" ( ( CBlockItem list )  Reversed)", 2),
  (" (CBlockItem)", 2),
  (" (CBlockItem)", 3),
  (" (CFunDef)", 5),
  (" ( ( Ident list )  Reversed)", 2),
  (" (CStat)", 2),
  (" (CStat)", 3),
  (" (CStat)", 4),
  (" (CStat)", 5),
  (" (CAsmStmt)", 4),
  (" (CTypeQual Maybe)", 2),
  (" (CAsmOperand list)", 2),
  (" ( ( CAsmOperand list )  Reversed)", 2),
  (" (CAsmOperand)", 3),
  (" ( ( CStrLit list )  Reversed)", 2),
  (" (CDecl)", 5),
  (" ( ( CDecl list )  Reversed)", 2),
  (" (CDecl)", 5),
  (" ( ( CStrLit Maybe * CAttr list ) )", 1),
  (" (CDecl)", 3),
  (" (CDeclSpec list)", 3),
  (" ( ( CDeclSpec list )  Reversed)", 6),
  (" (CDeclSpec)", 4),
  (" (CDeclSpec)", 3),
  (" (CStorageSpec)", 6),
  (" (CFunSpec)", 2),
  (" (CAlignSpec)", 2),
  (" (CDeclSpec list)", 3),
  (" (CTypeSpec)", 12),
  (" ( ( CDeclSpec list )  Reversed)", 5),
  (" ( ( CDeclSpec list )  Reversed)", 7),
  (" ( ( CDeclSpec list )  Reversed)", 4),
  (" ( ( CDeclSpec list )  Reversed)", 6),
  (" ( ( CDeclSpec list )  Reversed)", 6),
  (" ( ( CDeclSpec list )  Reversed)", 14),
  (" (CTypeSpec)", 2),
  (" (CStructUnion)", 3),
  (" (CStructTag Located)", 2),
  (" ( ( CDecl list )  Reversed)", 3),
  (" (CDecl)", 3),
  (" (CDecl)", 3),
  (" (CDecl)", 3),
  (" ( ( CDeclr Maybe * CExpr Maybe ) )", 3),
  (" ( ( CDeclr Maybe * CExpr Maybe ) )", 4),
  (" (CEnum)", 5),
  (" ( ( ((Ident * CExpr Maybe)) list )  Reversed)", 2),
  (" ( ( Ident * CExpr Maybe ) )", 4),
  (" (CTypeQual)", 6),
  (" ( ( CTypeQual list )  Reversed)", 3),
  (" (CDeclrR)", 2),
  (" (CStrLit Maybe)", 2),
  (" (CDeclrR)", 2),
  (" (CDeclrR)", 3),
  (" (CDeclrR)", 5),
  (" (CDeclrR)", 4),
  (" (CDeclrR)", 7),
  (" (CDeclrR)", 3),
  (" (CDeclrR)", 2),
  (" (CDeclrR)", 2),
  (" (CDeclrR)", 5),
  (" (CDeclrR)", 5),
  (" (CDeclrR)", 3),
  (" (CDeclr)", 1),
  (" (CDeclrR)", 3),
  (" (CDeclrR)", 3),
  (" ( ( CDecl list * Bool ) )", 3),
  (" ( ( CDecl list )  Reversed)", 2),
  (" (CDecl)", 15),
  (" ( ( Ident list )  Reversed)", 2),
  (" (CDecl)", 4),
  (" (CDeclrR)", 3),
  (" ( ( CDeclrR -> CDeclrR ) )", 2),
  (" ( ( CDeclrR -> CDeclrR ) )", 2),
  (" ( ( CDeclrR -> CDeclrR ) )", 11),
  (" (CDeclrR)", 6),
  (" (CDeclrR)", 9),
  (" (CInit)", 3),
  (" (CInit Maybe)", 2),
  (" (CInitList Reversed)", 5),
  (" (CDesignator list)", 3),
  (" ( ( CDesignator list )  Reversed)", 2),
  (" (CDesignator)", 3),
  (" (CDesignator)", 1),
  (" (CExpr)", 9),
  (" ( ( ((CDecl Maybe * CExpr)) list )  Reversed)", 2),
  (" ( ( CDecl Maybe * CExpr ) )", 2),
  (" ( ( CDesignator list )  Reversed)", 3),
  (" (CExpr)", 10),
  (" ( ( CExpr list )  Reversed)", 2),
  (" (CExpr)", 12),
  (" (CUnaryOp Located)", 6),
  (" (CExpr)", 2),
  (" (CExpr)", 4),
  (" (CExpr)", 3),
  (" (CExpr)", 3),
  (" (CExpr)", 5),
  (" (CExpr)", 3),
  (" (CExpr)", 2),
  (" (CExpr)", 2),
  (" (CExpr)", 2),
  (" (CExpr)", 2),
  (" (CExpr)", 2),
  (" (CExpr)", 3),
  (" (CExpr)", 2),
  (" (CAssignOp Located)", 11),
  (" (CExpr)", 2),
  (" ( ( CExpr list )  Reversed)", 2),
  (" (CExpr Maybe)", 2),
  (" (CExpr Maybe)", 2),
  (" (CExpr)", 1),
  (" (CConst)", 3),
  (" (CStrLit)", 2),
  (" ( ( CString list )  Reversed)", 2),
  (" (ClangCVersion)", 1),
  (" (Ident)", 2),
  (" (CAttr list)", 2),
  (" (CAttr list)", 2),
  (" (CAttr list)", 1),
  (" ( ( CAttr list )  Reversed)", 2),
  (" (CAttr Maybe)", 5),
  (" ( ( CExpr list )  Reversed)", 6),
  ("", 0)]
val string_reduce = find_list "reduce type not found" (fn name => fn occ => name ^ Int.toString (occ + 1)) [
  ("start_happy", 4),
  ("translation_unit", 1),
  ("ext_decl_list", 3),
  ("external_declaration", 4),
  ("function_definition", 14),
  ("function_declarator", 1),
  ("statement", 7),
  ("labeled_statement", 4),
  ("compound_statement", 2),
  ("enter_scope", 1),
  ("leave_scope", 1),
  ("block_item_list", 2),
  ("block_item", 2),
  ("nested_declaration", 3),
  ("nested_function_definition", 5),
  ("label_declarations", 2),
  ("expression_statement", 2),
  ("selection_statement", 3),
  ("iteration_statement", 4),
  ("jump_statement", 5),
  ("asm_statement", 4),
  ("maybe_type_qualifier", 2),
  ("asm_operands", 2),
  ("nonnull_asm_operands", 2),
  ("asm_operand", 3),
  ("asm_clobbers", 2),
  ("declaration", 5),
  ("declaration_list", 2),
  ("default_declaring_list", 5),
  ("asm_attrs_opt", 1),
  ("declaring_list", 3),
  ("declaration_specifier", 3),
  ("declaration_qualifier_list", 6),
  ("declaration_qualifier", 4),
  ("declaration_qualifier_without_types", 3),
  ("storage_class", 6),
  ("function_specifier", 2),
  ("alignment_specifier", 2),
  ("type_specifier", 3),
  ("basic_type_name", 12),
  ("basic_declaration_specifier", 5),
  ("basic_type_specifier", 7),
  ("sue_declaration_specifier", 4),
  ("sue_type_specifier", 6),
  ("typedef_declaration_specifier", 6),
  ("typedef_type_specifier", 14),
  ("elaborated_type_name", 2),
  ("struct_or_union_specifier", 3),
  ("struct_or_union", 2),
  ("struct_declaration_list", 3),
  ("struct_declaration", 3),
  ("struct_default_declaring_list", 3),
  ("struct_declaring_list", 3),
  ("struct_declarator", 3),
  ("struct_identifier_declarator", 4),
  ("enum_specifier", 5),
  ("enumerator_list", 2),
  ("enumerator", 4),
  ("type_qualifier", 6),
  ("type_qualifier_list", 3),
  ("declarator", 2),
  ("asm_opt", 2),
  ("typedef_declarator", 2),
  ("parameter_typedef_declarator", 3),
  ("clean_typedef_declarator", 5),
  ("clean_postfix_typedef_declarator", 4),
  ("paren_typedef_declarator", 7),
  ("paren_postfix_typedef_declarator", 3),
  ("simple_paren_typedef_declarator", 2),
  ("identifier_declarator", 2),
  ("unary_identifier_declarator", 5),
  ("postfix_identifier_declarator", 5),
  ("paren_identifier_declarator", 3),
  ("function_declarator_old", 1),
  ("old_function_declarator", 3),
  ("postfix_old_function_declarator", 3),
  ("parameter_type_list", 3),
  ("parameter_list", 2),
  ("parameter_declaration", 15),
  ("identifier_list", 2),
  ("type_name", 4),
  ("abstract_declarator", 3),
  ("postfixing_abstract_declarator", 2),
  ("array_abstract_declarator", 2),
  ("postfix_array_abstract_declarator", 11),
  ("unary_abstract_declarator", 6),
  ("postfix_abstract_declarator", 9),
  ("initializer", 3),
  ("initializer_opt", 2),
  ("initializer_list", 5),
  ("designation", 3),
  ("designator_list", 2),
  ("designator", 3),
  ("array_designator", 1),
  ("primary_expression", 9),
  ("generic_assoc_list", 2),
  ("generic_assoc", 2),
  ("offsetof_member_designator", 3),
  ("postfix_expression", 10),
  ("argument_expression_list", 2),
  ("unary_expression", 12),
  ("unary_operator", 6),
  ("cast_expression", 2),
  ("multiplicative_expression", 4),
  ("additive_expression", 3),
  ("shift_expression", 3),
  ("relational_expression", 5),
  ("equality_expression", 3),
  ("and_expression", 2),
  ("exclusive_or_expression", 2),
  ("inclusive_or_expression", 2),
  ("logical_and_expression", 2),
  ("logical_or_expression", 2),
  ("conditional_expression", 3),
  ("assignment_expression", 2),
  ("assignment_operator", 11),
  ("expression", 2),
  ("comma_expression", 2),
  ("expression_opt", 2),
  ("assignment_expression_opt", 2),
  ("constant_expression", 1),
  ("constant", 3),
  ("string_literal", 2),
  ("string_literal_list", 2),
  ("clang_version_literal", 1),
  ("identifier", 2),
  ("attrs_opt", 2),
  ("attrs", 2),
  ("attr", 1),
  ("attribute_list", 2),
  ("attribute", 5),
  ("attribute_params", 6),
  ("", 0)]
val reduce0 = fn start_happy x => x | _ => error "Only expecting start_happy"
val reduce1 = fn start_happy x => x | _ => error "Only expecting start_happy"
val reduce2 = fn start_happy x => x | _ => error "Only expecting start_happy"
val reduce3 = fn start_happy x => x | _ => error "Only expecting start_happy"
val reduce4 = fn translation_unit x => x | _ => error "Only expecting translation_unit"
val reduce5 = fn ext_decl_list x => x | _ => error "Only expecting ext_decl_list"
val reduce6 = fn ext_decl_list x => x | _ => error "Only expecting ext_decl_list"
val reduce7 = fn ext_decl_list x => x | _ => error "Only expecting ext_decl_list"
val reduce8 = fn external_declaration x => x | _ => error "Only expecting external_declaration"
val reduce9 = fn external_declaration x => x | _ => error "Only expecting external_declaration"
val reduce10 = fn external_declaration x => x | _ => error "Only expecting external_declaration"
val reduce11 = fn external_declaration x => x | _ => error "Only expecting external_declaration"
val reduce12 = fn function_definition x => x | _ => error "Only expecting function_definition"
val reduce13 = fn function_definition x => x | _ => error "Only expecting function_definition"
val reduce14 = fn function_definition x => x | _ => error "Only expecting function_definition"
val reduce15 = fn function_definition x => x | _ => error "Only expecting function_definition"
val reduce16 = fn function_definition x => x | _ => error "Only expecting function_definition"
val reduce17 = fn function_definition x => x | _ => error "Only expecting function_definition"
val reduce18 = fn function_definition x => x | _ => error "Only expecting function_definition"
val reduce19 = fn function_definition x => x | _ => error "Only expecting function_definition"
val reduce20 = fn function_definition x => x | _ => error "Only expecting function_definition"
val reduce21 = fn function_definition x => x | _ => error "Only expecting function_definition"
val reduce22 = fn function_definition x => x | _ => error "Only expecting function_definition"
val reduce23 = fn function_definition x => x | _ => error "Only expecting function_definition"
val reduce24 = fn function_definition x => x | _ => error "Only expecting function_definition"
val reduce25 = fn function_definition x => x | _ => error "Only expecting function_definition"
val reduce26 = fn function_declarator x => x | _ => error "Only expecting function_declarator"
val reduce27 = fn statement x => x | _ => error "Only expecting statement"
val reduce28 = fn statement x => x | _ => error "Only expecting statement"
val reduce29 = fn statement x => x | _ => error "Only expecting statement"
val reduce30 = fn statement x => x | _ => error "Only expecting statement"
val reduce31 = fn statement x => x | _ => error "Only expecting statement"
val reduce32 = fn statement x => x | _ => error "Only expecting statement"
val reduce33 = fn statement x => x | _ => error "Only expecting statement"
val reduce34 = fn labeled_statement x => x | _ => error "Only expecting labeled_statement"
val reduce35 = fn labeled_statement x => x | _ => error "Only expecting labeled_statement"
val reduce36 = fn labeled_statement x => x | _ => error "Only expecting labeled_statement"
val reduce37 = fn labeled_statement x => x | _ => error "Only expecting labeled_statement"
val reduce38 = fn compound_statement x => x | _ => error "Only expecting compound_statement"
val reduce39 = fn compound_statement x => x | _ => error "Only expecting compound_statement"
val reduce40 = fn enter_scope x => x | _ => error "Only expecting enter_scope"
val reduce41 = fn leave_scope x => x | _ => error "Only expecting leave_scope"
val reduce42 = fn block_item_list x => x | _ => error "Only expecting block_item_list"
val reduce43 = fn block_item_list x => x | _ => error "Only expecting block_item_list"
val reduce44 = fn block_item x => x | _ => error "Only expecting block_item"
val reduce45 = fn block_item x => x | _ => error "Only expecting block_item"
val reduce46 = fn nested_declaration x => x | _ => error "Only expecting nested_declaration"
val reduce47 = fn nested_declaration x => x | _ => error "Only expecting nested_declaration"
val reduce48 = fn nested_declaration x => x | _ => error "Only expecting nested_declaration"
val reduce49 = fn nested_function_definition x => x | _ => error "Only expecting nested_function_definition"
val reduce50 = fn nested_function_definition x => x | _ => error "Only expecting nested_function_definition"
val reduce51 = fn nested_function_definition x => x | _ => error "Only expecting nested_function_definition"
val reduce52 = fn nested_function_definition x => x | _ => error "Only expecting nested_function_definition"
val reduce53 = fn nested_function_definition x => x | _ => error "Only expecting nested_function_definition"
val reduce54 = fn label_declarations x => x | _ => error "Only expecting label_declarations"
val reduce55 = fn label_declarations x => x | _ => error "Only expecting label_declarations"
val reduce56 = fn expression_statement x => x | _ => error "Only expecting expression_statement"
val reduce57 = fn expression_statement x => x | _ => error "Only expecting expression_statement"
val reduce58 = fn selection_statement x => x | _ => error "Only expecting selection_statement"
val reduce59 = fn selection_statement x => x | _ => error "Only expecting selection_statement"
val reduce60 = fn selection_statement x => x | _ => error "Only expecting selection_statement"
val reduce61 = fn iteration_statement x => x | _ => error "Only expecting iteration_statement"
val reduce62 = fn iteration_statement x => x | _ => error "Only expecting iteration_statement"
val reduce63 = fn iteration_statement x => x | _ => error "Only expecting iteration_statement"
val reduce64 = fn iteration_statement x => x | _ => error "Only expecting iteration_statement"
val reduce65 = fn jump_statement x => x | _ => error "Only expecting jump_statement"
val reduce66 = fn jump_statement x => x | _ => error "Only expecting jump_statement"
val reduce67 = fn jump_statement x => x | _ => error "Only expecting jump_statement"
val reduce68 = fn jump_statement x => x | _ => error "Only expecting jump_statement"
val reduce69 = fn jump_statement x => x | _ => error "Only expecting jump_statement"
val reduce70 = fn asm_statement x => x | _ => error "Only expecting asm_statement"
val reduce71 = fn asm_statement x => x | _ => error "Only expecting asm_statement"
val reduce72 = fn asm_statement x => x | _ => error "Only expecting asm_statement"
val reduce73 = fn asm_statement x => x | _ => error "Only expecting asm_statement"
val reduce74 = fn maybe_type_qualifier x => x | _ => error "Only expecting maybe_type_qualifier"
val reduce75 = fn maybe_type_qualifier x => x | _ => error "Only expecting maybe_type_qualifier"
val reduce76 = fn asm_operands x => x | _ => error "Only expecting asm_operands"
val reduce77 = fn asm_operands x => x | _ => error "Only expecting asm_operands"
val reduce78 = fn nonnull_asm_operands x => x | _ => error "Only expecting nonnull_asm_operands"
val reduce79 = fn nonnull_asm_operands x => x | _ => error "Only expecting nonnull_asm_operands"
val reduce80 = fn asm_operand x => x | _ => error "Only expecting asm_operand"
val reduce81 = fn asm_operand x => x | _ => error "Only expecting asm_operand"
val reduce82 = fn asm_operand x => x | _ => error "Only expecting asm_operand"
val reduce83 = fn asm_clobbers x => x | _ => error "Only expecting asm_clobbers"
val reduce84 = fn asm_clobbers x => x | _ => error "Only expecting asm_clobbers"
val reduce85 = fn declaration x => x | _ => error "Only expecting declaration"
val reduce86 = fn declaration x => x | _ => error "Only expecting declaration"
val reduce87 = fn declaration x => x | _ => error "Only expecting declaration"
val reduce88 = fn declaration x => x | _ => error "Only expecting declaration"
val reduce89 = fn declaration x => x | _ => error "Only expecting declaration"
val reduce90 = fn declaration_list x => x | _ => error "Only expecting declaration_list"
val reduce91 = fn declaration_list x => x | _ => error "Only expecting declaration_list"
val reduce92 = fn default_declaring_list x => x | _ => error "Only expecting default_declaring_list"
val reduce93 = fn default_declaring_list x => x | _ => error "Only expecting default_declaring_list"
val reduce94 = fn default_declaring_list x => x | _ => error "Only expecting default_declaring_list"
val reduce95 = fn default_declaring_list x => x | _ => error "Only expecting default_declaring_list"
val reduce96 = fn default_declaring_list x => x | _ => error "Only expecting default_declaring_list"
val reduce97 = fn asm_attrs_opt x => x | _ => error "Only expecting asm_attrs_opt"
val reduce98 = fn declaring_list x => x | _ => error "Only expecting declaring_list"
val reduce99 = fn declaring_list x => x | _ => error "Only expecting declaring_list"
val reduce100 = fn declaring_list x => x | _ => error "Only expecting declaring_list"
val reduce101 = fn declaration_specifier x => x | _ => error "Only expecting declaration_specifier"
val reduce102 = fn declaration_specifier x => x | _ => error "Only expecting declaration_specifier"
val reduce103 = fn declaration_specifier x => x | _ => error "Only expecting declaration_specifier"
val reduce104 = fn declaration_qualifier_list x => x | _ => error "Only expecting declaration_qualifier_list"
val reduce105 = fn declaration_qualifier_list x => x | _ => error "Only expecting declaration_qualifier_list"
val reduce106 = fn declaration_qualifier_list x => x | _ => error "Only expecting declaration_qualifier_list"
val reduce107 = fn declaration_qualifier_list x => x | _ => error "Only expecting declaration_qualifier_list"
val reduce108 = fn declaration_qualifier_list x => x | _ => error "Only expecting declaration_qualifier_list"
val reduce109 = fn declaration_qualifier_list x => x | _ => error "Only expecting declaration_qualifier_list"
val reduce110 = fn declaration_qualifier x => x | _ => error "Only expecting declaration_qualifier"
val reduce111 = fn declaration_qualifier x => x | _ => error "Only expecting declaration_qualifier"
val reduce112 = fn declaration_qualifier x => x | _ => error "Only expecting declaration_qualifier"
val reduce113 = fn declaration_qualifier x => x | _ => error "Only expecting declaration_qualifier"
val reduce114 = fn declaration_qualifier_without_types x => x | _ => error "Only expecting declaration_qualifier_without_types"
val reduce115 = fn declaration_qualifier_without_types x => x | _ => error "Only expecting declaration_qualifier_without_types"
val reduce116 = fn declaration_qualifier_without_types x => x | _ => error "Only expecting declaration_qualifier_without_types"
val reduce117 = fn storage_class x => x | _ => error "Only expecting storage_class"
val reduce118 = fn storage_class x => x | _ => error "Only expecting storage_class"
val reduce119 = fn storage_class x => x | _ => error "Only expecting storage_class"
val reduce120 = fn storage_class x => x | _ => error "Only expecting storage_class"
val reduce121 = fn storage_class x => x | _ => error "Only expecting storage_class"
val reduce122 = fn storage_class x => x | _ => error "Only expecting storage_class"
val reduce123 = fn function_specifier x => x | _ => error "Only expecting function_specifier"
val reduce124 = fn function_specifier x => x | _ => error "Only expecting function_specifier"
val reduce125 = fn alignment_specifier x => x | _ => error "Only expecting alignment_specifier"
val reduce126 = fn alignment_specifier x => x | _ => error "Only expecting alignment_specifier"
val reduce127 = fn type_specifier x => x | _ => error "Only expecting type_specifier"
val reduce128 = fn type_specifier x => x | _ => error "Only expecting type_specifier"
val reduce129 = fn type_specifier x => x | _ => error "Only expecting type_specifier"
val reduce130 = fn basic_type_name x => x | _ => error "Only expecting basic_type_name"
val reduce131 = fn basic_type_name x => x | _ => error "Only expecting basic_type_name"
val reduce132 = fn basic_type_name x => x | _ => error "Only expecting basic_type_name"
val reduce133 = fn basic_type_name x => x | _ => error "Only expecting basic_type_name"
val reduce134 = fn basic_type_name x => x | _ => error "Only expecting basic_type_name"
val reduce135 = fn basic_type_name x => x | _ => error "Only expecting basic_type_name"
val reduce136 = fn basic_type_name x => x | _ => error "Only expecting basic_type_name"
val reduce137 = fn basic_type_name x => x | _ => error "Only expecting basic_type_name"
val reduce138 = fn basic_type_name x => x | _ => error "Only expecting basic_type_name"
val reduce139 = fn basic_type_name x => x | _ => error "Only expecting basic_type_name"
val reduce140 = fn basic_type_name x => x | _ => error "Only expecting basic_type_name"
val reduce141 = fn basic_type_name x => x | _ => error "Only expecting basic_type_name"
val reduce142 = fn basic_declaration_specifier x => x | _ => error "Only expecting basic_declaration_specifier"
val reduce143 = fn basic_declaration_specifier x => x | _ => error "Only expecting basic_declaration_specifier"
val reduce144 = fn basic_declaration_specifier x => x | _ => error "Only expecting basic_declaration_specifier"
val reduce145 = fn basic_declaration_specifier x => x | _ => error "Only expecting basic_declaration_specifier"
val reduce146 = fn basic_declaration_specifier x => x | _ => error "Only expecting basic_declaration_specifier"
val reduce147 = fn basic_type_specifier x => x | _ => error "Only expecting basic_type_specifier"
val reduce148 = fn basic_type_specifier x => x | _ => error "Only expecting basic_type_specifier"
val reduce149 = fn basic_type_specifier x => x | _ => error "Only expecting basic_type_specifier"
val reduce150 = fn basic_type_specifier x => x | _ => error "Only expecting basic_type_specifier"
val reduce151 = fn basic_type_specifier x => x | _ => error "Only expecting basic_type_specifier"
val reduce152 = fn basic_type_specifier x => x | _ => error "Only expecting basic_type_specifier"
val reduce153 = fn basic_type_specifier x => x | _ => error "Only expecting basic_type_specifier"
val reduce154 = fn sue_declaration_specifier x => x | _ => error "Only expecting sue_declaration_specifier"
val reduce155 = fn sue_declaration_specifier x => x | _ => error "Only expecting sue_declaration_specifier"
val reduce156 = fn sue_declaration_specifier x => x | _ => error "Only expecting sue_declaration_specifier"
val reduce157 = fn sue_declaration_specifier x => x | _ => error "Only expecting sue_declaration_specifier"
val reduce158 = fn sue_type_specifier x => x | _ => error "Only expecting sue_type_specifier"
val reduce159 = fn sue_type_specifier x => x | _ => error "Only expecting sue_type_specifier"
val reduce160 = fn sue_type_specifier x => x | _ => error "Only expecting sue_type_specifier"
val reduce161 = fn sue_type_specifier x => x | _ => error "Only expecting sue_type_specifier"
val reduce162 = fn sue_type_specifier x => x | _ => error "Only expecting sue_type_specifier"
val reduce163 = fn sue_type_specifier x => x | _ => error "Only expecting sue_type_specifier"
val reduce164 = fn typedef_declaration_specifier x => x | _ => error "Only expecting typedef_declaration_specifier"
val reduce165 = fn typedef_declaration_specifier x => x | _ => error "Only expecting typedef_declaration_specifier"
val reduce166 = fn typedef_declaration_specifier x => x | _ => error "Only expecting typedef_declaration_specifier"
val reduce167 = fn typedef_declaration_specifier x => x | _ => error "Only expecting typedef_declaration_specifier"
val reduce168 = fn typedef_declaration_specifier x => x | _ => error "Only expecting typedef_declaration_specifier"
val reduce169 = fn typedef_declaration_specifier x => x | _ => error "Only expecting typedef_declaration_specifier"
val reduce170 = fn typedef_type_specifier x => x | _ => error "Only expecting typedef_type_specifier"
val reduce171 = fn typedef_type_specifier x => x | _ => error "Only expecting typedef_type_specifier"
val reduce172 = fn typedef_type_specifier x => x | _ => error "Only expecting typedef_type_specifier"
val reduce173 = fn typedef_type_specifier x => x | _ => error "Only expecting typedef_type_specifier"
val reduce174 = fn typedef_type_specifier x => x | _ => error "Only expecting typedef_type_specifier"
val reduce175 = fn typedef_type_specifier x => x | _ => error "Only expecting typedef_type_specifier"
val reduce176 = fn typedef_type_specifier x => x | _ => error "Only expecting typedef_type_specifier"
val reduce177 = fn typedef_type_specifier x => x | _ => error "Only expecting typedef_type_specifier"
val reduce178 = fn typedef_type_specifier x => x | _ => error "Only expecting typedef_type_specifier"
val reduce179 = fn typedef_type_specifier x => x | _ => error "Only expecting typedef_type_specifier"
val reduce180 = fn typedef_type_specifier x => x | _ => error "Only expecting typedef_type_specifier"
val reduce181 = fn typedef_type_specifier x => x | _ => error "Only expecting typedef_type_specifier"
val reduce182 = fn typedef_type_specifier x => x | _ => error "Only expecting typedef_type_specifier"
val reduce183 = fn typedef_type_specifier x => x | _ => error "Only expecting typedef_type_specifier"
val reduce184 = fn elaborated_type_name x => x | _ => error "Only expecting elaborated_type_name"
val reduce185 = fn elaborated_type_name x => x | _ => error "Only expecting elaborated_type_name"
val reduce186 = fn struct_or_union_specifier x => x | _ => error "Only expecting struct_or_union_specifier"
val reduce187 = fn struct_or_union_specifier x => x | _ => error "Only expecting struct_or_union_specifier"
val reduce188 = fn struct_or_union_specifier x => x | _ => error "Only expecting struct_or_union_specifier"
val reduce189 = fn struct_or_union x => x | _ => error "Only expecting struct_or_union"
val reduce190 = fn struct_or_union x => x | _ => error "Only expecting struct_or_union"
val reduce191 = fn struct_declaration_list x => x | _ => error "Only expecting struct_declaration_list"
val reduce192 = fn struct_declaration_list x => x | _ => error "Only expecting struct_declaration_list"
val reduce193 = fn struct_declaration_list x => x | _ => error "Only expecting struct_declaration_list"
val reduce194 = fn struct_declaration x => x | _ => error "Only expecting struct_declaration"
val reduce195 = fn struct_declaration x => x | _ => error "Only expecting struct_declaration"
val reduce196 = fn struct_declaration x => x | _ => error "Only expecting struct_declaration"
val reduce197 = fn struct_default_declaring_list x => x | _ => error "Only expecting struct_default_declaring_list"
val reduce198 = fn struct_default_declaring_list x => x | _ => error "Only expecting struct_default_declaring_list"
val reduce199 = fn struct_default_declaring_list x => x | _ => error "Only expecting struct_default_declaring_list"
val reduce200 = fn struct_declaring_list x => x | _ => error "Only expecting struct_declaring_list"
val reduce201 = fn struct_declaring_list x => x | _ => error "Only expecting struct_declaring_list"
val reduce202 = fn struct_declaring_list x => x | _ => error "Only expecting struct_declaring_list"
val reduce203 = fn struct_declarator x => x | _ => error "Only expecting struct_declarator"
val reduce204 = fn struct_declarator x => x | _ => error "Only expecting struct_declarator"
val reduce205 = fn struct_declarator x => x | _ => error "Only expecting struct_declarator"
val reduce206 = fn struct_identifier_declarator x => x | _ => error "Only expecting struct_identifier_declarator"
val reduce207 = fn struct_identifier_declarator x => x | _ => error "Only expecting struct_identifier_declarator"
val reduce208 = fn struct_identifier_declarator x => x | _ => error "Only expecting struct_identifier_declarator"
val reduce209 = fn struct_identifier_declarator x => x | _ => error "Only expecting struct_identifier_declarator"
val reduce210 = fn enum_specifier x => x | _ => error "Only expecting enum_specifier"
val reduce211 = fn enum_specifier x => x | _ => error "Only expecting enum_specifier"
val reduce212 = fn enum_specifier x => x | _ => error "Only expecting enum_specifier"
val reduce213 = fn enum_specifier x => x | _ => error "Only expecting enum_specifier"
val reduce214 = fn enum_specifier x => x | _ => error "Only expecting enum_specifier"
val reduce215 = fn enumerator_list x => x | _ => error "Only expecting enumerator_list"
val reduce216 = fn enumerator_list x => x | _ => error "Only expecting enumerator_list"
val reduce217 = fn enumerator x => x | _ => error "Only expecting enumerator"
val reduce218 = fn enumerator x => x | _ => error "Only expecting enumerator"
val reduce219 = fn enumerator x => x | _ => error "Only expecting enumerator"
val reduce220 = fn enumerator x => x | _ => error "Only expecting enumerator"
val reduce221 = fn type_qualifier x => x | _ => error "Only expecting type_qualifier"
val reduce222 = fn type_qualifier x => x | _ => error "Only expecting type_qualifier"
val reduce223 = fn type_qualifier x => x | _ => error "Only expecting type_qualifier"
val reduce224 = fn type_qualifier x => x | _ => error "Only expecting type_qualifier"
val reduce225 = fn type_qualifier x => x | _ => error "Only expecting type_qualifier"
val reduce226 = fn type_qualifier x => x | _ => error "Only expecting type_qualifier"
val reduce227 = fn type_qualifier_list x => x | _ => error "Only expecting type_qualifier_list"
val reduce228 = fn type_qualifier_list x => x | _ => error "Only expecting type_qualifier_list"
val reduce229 = fn type_qualifier_list x => x | _ => error "Only expecting type_qualifier_list"
val reduce230 = fn declarator x => x | _ => error "Only expecting declarator"
val reduce231 = fn declarator x => x | _ => error "Only expecting declarator"
val reduce232 = fn asm_opt x => x | _ => error "Only expecting asm_opt"
val reduce233 = fn asm_opt x => x | _ => error "Only expecting asm_opt"
val reduce234 = fn typedef_declarator x => x | _ => error "Only expecting typedef_declarator"
val reduce235 = fn typedef_declarator x => x | _ => error "Only expecting typedef_declarator"
val reduce236 = fn parameter_typedef_declarator x => x | _ => error "Only expecting parameter_typedef_declarator"
val reduce237 = fn parameter_typedef_declarator x => x | _ => error "Only expecting parameter_typedef_declarator"
val reduce238 = fn parameter_typedef_declarator x => x | _ => error "Only expecting parameter_typedef_declarator"
val reduce239 = fn clean_typedef_declarator x => x | _ => error "Only expecting clean_typedef_declarator"
val reduce240 = fn clean_typedef_declarator x => x | _ => error "Only expecting clean_typedef_declarator"
val reduce241 = fn clean_typedef_declarator x => x | _ => error "Only expecting clean_typedef_declarator"
val reduce242 = fn clean_typedef_declarator x => x | _ => error "Only expecting clean_typedef_declarator"
val reduce243 = fn clean_typedef_declarator x => x | _ => error "Only expecting clean_typedef_declarator"
val reduce244 = fn clean_postfix_typedef_declarator x => x | _ => error "Only expecting clean_postfix_typedef_declarator"
val reduce245 = fn clean_postfix_typedef_declarator x => x | _ => error "Only expecting clean_postfix_typedef_declarator"
val reduce246 = fn clean_postfix_typedef_declarator x => x | _ => error "Only expecting clean_postfix_typedef_declarator"
val reduce247 = fn clean_postfix_typedef_declarator x => x | _ => error "Only expecting clean_postfix_typedef_declarator"
val reduce248 = fn paren_typedef_declarator x => x | _ => error "Only expecting paren_typedef_declarator"
val reduce249 = fn paren_typedef_declarator x => x | _ => error "Only expecting paren_typedef_declarator"
val reduce250 = fn paren_typedef_declarator x => x | _ => error "Only expecting paren_typedef_declarator"
val reduce251 = fn paren_typedef_declarator x => x | _ => error "Only expecting paren_typedef_declarator"
val reduce252 = fn paren_typedef_declarator x => x | _ => error "Only expecting paren_typedef_declarator"
val reduce253 = fn paren_typedef_declarator x => x | _ => error "Only expecting paren_typedef_declarator"
val reduce254 = fn paren_typedef_declarator x => x | _ => error "Only expecting paren_typedef_declarator"
val reduce255 = fn paren_postfix_typedef_declarator x => x | _ => error "Only expecting paren_postfix_typedef_declarator"
val reduce256 = fn paren_postfix_typedef_declarator x => x | _ => error "Only expecting paren_postfix_typedef_declarator"
val reduce257 = fn paren_postfix_typedef_declarator x => x | _ => error "Only expecting paren_postfix_typedef_declarator"
val reduce258 = fn simple_paren_typedef_declarator x => x | _ => error "Only expecting simple_paren_typedef_declarator"
val reduce259 = fn simple_paren_typedef_declarator x => x | _ => error "Only expecting simple_paren_typedef_declarator"
val reduce260 = fn identifier_declarator x => x | _ => error "Only expecting identifier_declarator"
val reduce261 = fn identifier_declarator x => x | _ => error "Only expecting identifier_declarator"
val reduce262 = fn unary_identifier_declarator x => x | _ => error "Only expecting unary_identifier_declarator"
val reduce263 = fn unary_identifier_declarator x => x | _ => error "Only expecting unary_identifier_declarator"
val reduce264 = fn unary_identifier_declarator x => x | _ => error "Only expecting unary_identifier_declarator"
val reduce265 = fn unary_identifier_declarator x => x | _ => error "Only expecting unary_identifier_declarator"
val reduce266 = fn unary_identifier_declarator x => x | _ => error "Only expecting unary_identifier_declarator"
val reduce267 = fn postfix_identifier_declarator x => x | _ => error "Only expecting postfix_identifier_declarator"
val reduce268 = fn postfix_identifier_declarator x => x | _ => error "Only expecting postfix_identifier_declarator"
val reduce269 = fn postfix_identifier_declarator x => x | _ => error "Only expecting postfix_identifier_declarator"
val reduce270 = fn postfix_identifier_declarator x => x | _ => error "Only expecting postfix_identifier_declarator"
val reduce271 = fn postfix_identifier_declarator x => x | _ => error "Only expecting postfix_identifier_declarator"
val reduce272 = fn paren_identifier_declarator x => x | _ => error "Only expecting paren_identifier_declarator"
val reduce273 = fn paren_identifier_declarator x => x | _ => error "Only expecting paren_identifier_declarator"
val reduce274 = fn paren_identifier_declarator x => x | _ => error "Only expecting paren_identifier_declarator"
val reduce275 = fn function_declarator_old x => x | _ => error "Only expecting function_declarator_old"
val reduce276 = fn old_function_declarator x => x | _ => error "Only expecting old_function_declarator"
val reduce277 = fn old_function_declarator x => x | _ => error "Only expecting old_function_declarator"
val reduce278 = fn old_function_declarator x => x | _ => error "Only expecting old_function_declarator"
val reduce279 = fn postfix_old_function_declarator x => x | _ => error "Only expecting postfix_old_function_declarator"
val reduce280 = fn postfix_old_function_declarator x => x | _ => error "Only expecting postfix_old_function_declarator"
val reduce281 = fn postfix_old_function_declarator x => x | _ => error "Only expecting postfix_old_function_declarator"
val reduce282 = fn parameter_type_list x => x | _ => error "Only expecting parameter_type_list"
val reduce283 = fn parameter_type_list x => x | _ => error "Only expecting parameter_type_list"
val reduce284 = fn parameter_type_list x => x | _ => error "Only expecting parameter_type_list"
val reduce285 = fn parameter_list x => x | _ => error "Only expecting parameter_list"
val reduce286 = fn parameter_list x => x | _ => error "Only expecting parameter_list"
val reduce287 = fn parameter_declaration x => x | _ => error "Only expecting parameter_declaration"
val reduce288 = fn parameter_declaration x => x | _ => error "Only expecting parameter_declaration"
val reduce289 = fn parameter_declaration x => x | _ => error "Only expecting parameter_declaration"
val reduce290 = fn parameter_declaration x => x | _ => error "Only expecting parameter_declaration"
val reduce291 = fn parameter_declaration x => x | _ => error "Only expecting parameter_declaration"
val reduce292 = fn parameter_declaration x => x | _ => error "Only expecting parameter_declaration"
val reduce293 = fn parameter_declaration x => x | _ => error "Only expecting parameter_declaration"
val reduce294 = fn parameter_declaration x => x | _ => error "Only expecting parameter_declaration"
val reduce295 = fn parameter_declaration x => x | _ => error "Only expecting parameter_declaration"
val reduce296 = fn parameter_declaration x => x | _ => error "Only expecting parameter_declaration"
val reduce297 = fn parameter_declaration x => x | _ => error "Only expecting parameter_declaration"
val reduce298 = fn parameter_declaration x => x | _ => error "Only expecting parameter_declaration"
val reduce299 = fn parameter_declaration x => x | _ => error "Only expecting parameter_declaration"
val reduce300 = fn parameter_declaration x => x | _ => error "Only expecting parameter_declaration"
val reduce301 = fn parameter_declaration x => x | _ => error "Only expecting parameter_declaration"
val reduce302 = fn identifier_list x => x | _ => error "Only expecting identifier_list"
val reduce303 = fn identifier_list x => x | _ => error "Only expecting identifier_list"
val reduce304 = fn type_name x => x | _ => error "Only expecting type_name"
val reduce305 = fn type_name x => x | _ => error "Only expecting type_name"
val reduce306 = fn type_name x => x | _ => error "Only expecting type_name"
val reduce307 = fn type_name x => x | _ => error "Only expecting type_name"
val reduce308 = fn abstract_declarator x => x | _ => error "Only expecting abstract_declarator"
val reduce309 = fn abstract_declarator x => x | _ => error "Only expecting abstract_declarator"
val reduce310 = fn abstract_declarator x => x | _ => error "Only expecting abstract_declarator"
val reduce311 = fn postfixing_abstract_declarator x => x | _ => error "Only expecting postfixing_abstract_declarator"
val reduce312 = fn postfixing_abstract_declarator x => x | _ => error "Only expecting postfixing_abstract_declarator"
val reduce313 = fn array_abstract_declarator x => x | _ => error "Only expecting array_abstract_declarator"
val reduce314 = fn array_abstract_declarator x => x | _ => error "Only expecting array_abstract_declarator"
val reduce315 = fn postfix_array_abstract_declarator x => x | _ => error "Only expecting postfix_array_abstract_declarator"
val reduce316 = fn postfix_array_abstract_declarator x => x | _ => error "Only expecting postfix_array_abstract_declarator"
val reduce317 = fn postfix_array_abstract_declarator x => x | _ => error "Only expecting postfix_array_abstract_declarator"
val reduce318 = fn postfix_array_abstract_declarator x => x | _ => error "Only expecting postfix_array_abstract_declarator"
val reduce319 = fn postfix_array_abstract_declarator x => x | _ => error "Only expecting postfix_array_abstract_declarator"
val reduce320 = fn postfix_array_abstract_declarator x => x | _ => error "Only expecting postfix_array_abstract_declarator"
val reduce321 = fn postfix_array_abstract_declarator x => x | _ => error "Only expecting postfix_array_abstract_declarator"
val reduce322 = fn postfix_array_abstract_declarator x => x | _ => error "Only expecting postfix_array_abstract_declarator"
val reduce323 = fn postfix_array_abstract_declarator x => x | _ => error "Only expecting postfix_array_abstract_declarator"
val reduce324 = fn postfix_array_abstract_declarator x => x | _ => error "Only expecting postfix_array_abstract_declarator"
val reduce325 = fn postfix_array_abstract_declarator x => x | _ => error "Only expecting postfix_array_abstract_declarator"
val reduce326 = fn unary_abstract_declarator x => x | _ => error "Only expecting unary_abstract_declarator"
val reduce327 = fn unary_abstract_declarator x => x | _ => error "Only expecting unary_abstract_declarator"
val reduce328 = fn unary_abstract_declarator x => x | _ => error "Only expecting unary_abstract_declarator"
val reduce329 = fn unary_abstract_declarator x => x | _ => error "Only expecting unary_abstract_declarator"
val reduce330 = fn unary_abstract_declarator x => x | _ => error "Only expecting unary_abstract_declarator"
val reduce331 = fn unary_abstract_declarator x => x | _ => error "Only expecting unary_abstract_declarator"
val reduce332 = fn postfix_abstract_declarator x => x | _ => error "Only expecting postfix_abstract_declarator"
val reduce333 = fn postfix_abstract_declarator x => x | _ => error "Only expecting postfix_abstract_declarator"
val reduce334 = fn postfix_abstract_declarator x => x | _ => error "Only expecting postfix_abstract_declarator"
val reduce335 = fn postfix_abstract_declarator x => x | _ => error "Only expecting postfix_abstract_declarator"
val reduce336 = fn postfix_abstract_declarator x => x | _ => error "Only expecting postfix_abstract_declarator"
val reduce337 = fn postfix_abstract_declarator x => x | _ => error "Only expecting postfix_abstract_declarator"
val reduce338 = fn postfix_abstract_declarator x => x | _ => error "Only expecting postfix_abstract_declarator"
val reduce339 = fn postfix_abstract_declarator x => x | _ => error "Only expecting postfix_abstract_declarator"
val reduce340 = fn postfix_abstract_declarator x => x | _ => error "Only expecting postfix_abstract_declarator"
val reduce341 = fn initializer x => x | _ => error "Only expecting initializer"
val reduce342 = fn initializer x => x | _ => error "Only expecting initializer"
val reduce343 = fn initializer x => x | _ => error "Only expecting initializer"
val reduce344 = fn initializer_opt x => x | _ => error "Only expecting initializer_opt"
val reduce345 = fn initializer_opt x => x | _ => error "Only expecting initializer_opt"
val reduce346 = fn initializer_list x => x | _ => error "Only expecting initializer_list"
val reduce347 = fn initializer_list x => x | _ => error "Only expecting initializer_list"
val reduce348 = fn initializer_list x => x | _ => error "Only expecting initializer_list"
val reduce349 = fn initializer_list x => x | _ => error "Only expecting initializer_list"
val reduce350 = fn initializer_list x => x | _ => error "Only expecting initializer_list"
val reduce351 = fn designation x => x | _ => error "Only expecting designation"
val reduce352 = fn designation x => x | _ => error "Only expecting designation"
val reduce353 = fn designation x => x | _ => error "Only expecting designation"
val reduce354 = fn designator_list x => x | _ => error "Only expecting designator_list"
val reduce355 = fn designator_list x => x | _ => error "Only expecting designator_list"
val reduce356 = fn designator x => x | _ => error "Only expecting designator"
val reduce357 = fn designator x => x | _ => error "Only expecting designator"
val reduce358 = fn designator x => x | _ => error "Only expecting designator"
val reduce359 = fn array_designator x => x | _ => error "Only expecting array_designator"
val reduce360 = fn primary_expression x => x | _ => error "Only expecting primary_expression"
val reduce361 = fn primary_expression x => x | _ => error "Only expecting primary_expression"
val reduce362 = fn primary_expression x => x | _ => error "Only expecting primary_expression"
val reduce363 = fn primary_expression x => x | _ => error "Only expecting primary_expression"
val reduce364 = fn primary_expression x => x | _ => error "Only expecting primary_expression"
val reduce365 = fn primary_expression x => x | _ => error "Only expecting primary_expression"
val reduce366 = fn primary_expression x => x | _ => error "Only expecting primary_expression"
val reduce367 = fn primary_expression x => x | _ => error "Only expecting primary_expression"
val reduce368 = fn primary_expression x => x | _ => error "Only expecting primary_expression"
val reduce369 = fn generic_assoc_list x => x | _ => error "Only expecting generic_assoc_list"
val reduce370 = fn generic_assoc_list x => x | _ => error "Only expecting generic_assoc_list"
val reduce371 = fn generic_assoc x => x | _ => error "Only expecting generic_assoc"
val reduce372 = fn generic_assoc x => x | _ => error "Only expecting generic_assoc"
val reduce373 = fn offsetof_member_designator x => x | _ => error "Only expecting offsetof_member_designator"
val reduce374 = fn offsetof_member_designator x => x | _ => error "Only expecting offsetof_member_designator"
val reduce375 = fn offsetof_member_designator x => x | _ => error "Only expecting offsetof_member_designator"
val reduce376 = fn postfix_expression x => x | _ => error "Only expecting postfix_expression"
val reduce377 = fn postfix_expression x => x | _ => error "Only expecting postfix_expression"
val reduce378 = fn postfix_expression x => x | _ => error "Only expecting postfix_expression"
val reduce379 = fn postfix_expression x => x | _ => error "Only expecting postfix_expression"
val reduce380 = fn postfix_expression x => x | _ => error "Only expecting postfix_expression"
val reduce381 = fn postfix_expression x => x | _ => error "Only expecting postfix_expression"
val reduce382 = fn postfix_expression x => x | _ => error "Only expecting postfix_expression"
val reduce383 = fn postfix_expression x => x | _ => error "Only expecting postfix_expression"
val reduce384 = fn postfix_expression x => x | _ => error "Only expecting postfix_expression"
val reduce385 = fn postfix_expression x => x | _ => error "Only expecting postfix_expression"
val reduce386 = fn argument_expression_list x => x | _ => error "Only expecting argument_expression_list"
val reduce387 = fn argument_expression_list x => x | _ => error "Only expecting argument_expression_list"
val reduce388 = fn unary_expression x => x | _ => error "Only expecting unary_expression"
val reduce389 = fn unary_expression x => x | _ => error "Only expecting unary_expression"
val reduce390 = fn unary_expression x => x | _ => error "Only expecting unary_expression"
val reduce391 = fn unary_expression x => x | _ => error "Only expecting unary_expression"
val reduce392 = fn unary_expression x => x | _ => error "Only expecting unary_expression"
val reduce393 = fn unary_expression x => x | _ => error "Only expecting unary_expression"
val reduce394 = fn unary_expression x => x | _ => error "Only expecting unary_expression"
val reduce395 = fn unary_expression x => x | _ => error "Only expecting unary_expression"
val reduce396 = fn unary_expression x => x | _ => error "Only expecting unary_expression"
val reduce397 = fn unary_expression x => x | _ => error "Only expecting unary_expression"
val reduce398 = fn unary_expression x => x | _ => error "Only expecting unary_expression"
val reduce399 = fn unary_expression x => x | _ => error "Only expecting unary_expression"
val reduce400 = fn unary_operator x => x | _ => error "Only expecting unary_operator"
val reduce401 = fn unary_operator x => x | _ => error "Only expecting unary_operator"
val reduce402 = fn unary_operator x => x | _ => error "Only expecting unary_operator"
val reduce403 = fn unary_operator x => x | _ => error "Only expecting unary_operator"
val reduce404 = fn unary_operator x => x | _ => error "Only expecting unary_operator"
val reduce405 = fn unary_operator x => x | _ => error "Only expecting unary_operator"
val reduce406 = fn cast_expression x => x | _ => error "Only expecting cast_expression"
val reduce407 = fn cast_expression x => x | _ => error "Only expecting cast_expression"
val reduce408 = fn multiplicative_expression x => x | _ => error "Only expecting multiplicative_expression"
val reduce409 = fn multiplicative_expression x => x | _ => error "Only expecting multiplicative_expression"
val reduce410 = fn multiplicative_expression x => x | _ => error "Only expecting multiplicative_expression"
val reduce411 = fn multiplicative_expression x => x | _ => error "Only expecting multiplicative_expression"
val reduce412 = fn additive_expression x => x | _ => error "Only expecting additive_expression"
val reduce413 = fn additive_expression x => x | _ => error "Only expecting additive_expression"
val reduce414 = fn additive_expression x => x | _ => error "Only expecting additive_expression"
val reduce415 = fn shift_expression x => x | _ => error "Only expecting shift_expression"
val reduce416 = fn shift_expression x => x | _ => error "Only expecting shift_expression"
val reduce417 = fn shift_expression x => x | _ => error "Only expecting shift_expression"
val reduce418 = fn relational_expression x => x | _ => error "Only expecting relational_expression"
val reduce419 = fn relational_expression x => x | _ => error "Only expecting relational_expression"
val reduce420 = fn relational_expression x => x | _ => error "Only expecting relational_expression"
val reduce421 = fn relational_expression x => x | _ => error "Only expecting relational_expression"
val reduce422 = fn relational_expression x => x | _ => error "Only expecting relational_expression"
val reduce423 = fn equality_expression x => x | _ => error "Only expecting equality_expression"
val reduce424 = fn equality_expression x => x | _ => error "Only expecting equality_expression"
val reduce425 = fn equality_expression x => x | _ => error "Only expecting equality_expression"
val reduce426 = fn and_expression x => x | _ => error "Only expecting and_expression"
val reduce427 = fn and_expression x => x | _ => error "Only expecting and_expression"
val reduce428 = fn exclusive_or_expression x => x | _ => error "Only expecting exclusive_or_expression"
val reduce429 = fn exclusive_or_expression x => x | _ => error "Only expecting exclusive_or_expression"
val reduce430 = fn inclusive_or_expression x => x | _ => error "Only expecting inclusive_or_expression"
val reduce431 = fn inclusive_or_expression x => x | _ => error "Only expecting inclusive_or_expression"
val reduce432 = fn logical_and_expression x => x | _ => error "Only expecting logical_and_expression"
val reduce433 = fn logical_and_expression x => x | _ => error "Only expecting logical_and_expression"
val reduce434 = fn logical_or_expression x => x | _ => error "Only expecting logical_or_expression"
val reduce435 = fn logical_or_expression x => x | _ => error "Only expecting logical_or_expression"
val reduce436 = fn conditional_expression x => x | _ => error "Only expecting conditional_expression"
val reduce437 = fn conditional_expression x => x | _ => error "Only expecting conditional_expression"
val reduce438 = fn conditional_expression x => x | _ => error "Only expecting conditional_expression"
val reduce439 = fn assignment_expression x => x | _ => error "Only expecting assignment_expression"
val reduce440 = fn assignment_expression x => x | _ => error "Only expecting assignment_expression"
val reduce441 = fn assignment_operator x => x | _ => error "Only expecting assignment_operator"
val reduce442 = fn assignment_operator x => x | _ => error "Only expecting assignment_operator"
val reduce443 = fn assignment_operator x => x | _ => error "Only expecting assignment_operator"
val reduce444 = fn assignment_operator x => x | _ => error "Only expecting assignment_operator"
val reduce445 = fn assignment_operator x => x | _ => error "Only expecting assignment_operator"
val reduce446 = fn assignment_operator x => x | _ => error "Only expecting assignment_operator"
val reduce447 = fn assignment_operator x => x | _ => error "Only expecting assignment_operator"
val reduce448 = fn assignment_operator x => x | _ => error "Only expecting assignment_operator"
val reduce449 = fn assignment_operator x => x | _ => error "Only expecting assignment_operator"
val reduce450 = fn assignment_operator x => x | _ => error "Only expecting assignment_operator"
val reduce451 = fn assignment_operator x => x | _ => error "Only expecting assignment_operator"
val reduce452 = fn expression x => x | _ => error "Only expecting expression"
val reduce453 = fn expression x => x | _ => error "Only expecting expression"
val reduce454 = fn comma_expression x => x | _ => error "Only expecting comma_expression"
val reduce455 = fn comma_expression x => x | _ => error "Only expecting comma_expression"
val reduce456 = fn expression_opt x => x | _ => error "Only expecting expression_opt"
val reduce457 = fn expression_opt x => x | _ => error "Only expecting expression_opt"
val reduce458 = fn assignment_expression_opt x => x | _ => error "Only expecting assignment_expression_opt"
val reduce459 = fn assignment_expression_opt x => x | _ => error "Only expecting assignment_expression_opt"
val reduce460 = fn constant_expression x => x | _ => error "Only expecting constant_expression"
val reduce461 = fn constant x => x | _ => error "Only expecting constant"
val reduce462 = fn constant x => x | _ => error "Only expecting constant"
val reduce463 = fn constant x => x | _ => error "Only expecting constant"
val reduce464 = fn string_literal x => x | _ => error "Only expecting string_literal"
val reduce465 = fn string_literal x => x | _ => error "Only expecting string_literal"
val reduce466 = fn string_literal_list x => x | _ => error "Only expecting string_literal_list"
val reduce467 = fn string_literal_list x => x | _ => error "Only expecting string_literal_list"
val reduce468 = fn clang_version_literal x => x | _ => error "Only expecting clang_version_literal"
val reduce469 = fn identifier x => x | _ => error "Only expecting identifier"
val reduce470 = fn identifier x => x | _ => error "Only expecting identifier"
val reduce471 = fn attrs_opt x => x | _ => error "Only expecting attrs_opt"
val reduce472 = fn attrs_opt x => x | _ => error "Only expecting attrs_opt"
val reduce473 = fn attrs x => x | _ => error "Only expecting attrs"
val reduce474 = fn attrs x => x | _ => error "Only expecting attrs"
val reduce475 = fn attr x => x | _ => error "Only expecting attr"
val reduce476 = fn attribute_list x => x | _ => error "Only expecting attribute_list"
val reduce477 = fn attribute_list x => x | _ => error "Only expecting attribute_list"
val reduce478 = fn attribute x => x | _ => error "Only expecting attribute"
val reduce479 = fn attribute x => x | _ => error "Only expecting attribute"
val reduce480 = fn attribute x => x | _ => error "Only expecting attribute"
val reduce481 = fn attribute x => x | _ => error "Only expecting attribute"
val reduce482 = fn attribute x => x | _ => error "Only expecting attribute"
val reduce483 = fn attribute_params x => x | _ => error "Only expecting attribute_params"
val reduce484 = fn attribute_params x => x | _ => error "Only expecting attribute_params"
val reduce485 = fn attribute_params x => x | _ => error "Only expecting attribute_params"
val reduce486 = fn attribute_params x => x | _ => error "Only expecting attribute_params"
val reduce487 = fn attribute_params x => x | _ => error "Only expecting attribute_params"
val reduce488 = fn attribute_params x => x | _ => error "Only expecting attribute_params"
end
structure C_Grammar_Rule_Wrap = 
struct
(*#line 1.2 "c_grammar_fun.grm"*)open C_Ast open C_Grammar_Rule_Lib

type start_happy = (CTranslUnit, (CExtDecl, (CStat, (CExpr, unit) either) either) either) either

fun start_happy4 (x : start_happy) = case x of Right (Right (Right (Left x))) => SOME x | _ => NONE
fun start_happy3 (x : start_happy) = case x of Right (Right (Left x)) => SOME x | _ => NONE
fun start_happy2 (x : start_happy) = case x of Right (Left x) => SOME x | _ => NONE
fun start_happy1 (x : start_happy) = case x of Left x => SOME x | _ => NONE


(*#line 8775.1 "c_grammar_fun.grm.sml"*)
fun update_env _ = K (return ())
val start_happy1 : ( ( CTranslUnit, (CExtDecl, (CStat, (CExpr, unit) either) either) either )  either) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val start_happy2 : ( ( CTranslUnit, (CExtDecl, (CStat, (CExpr, unit) either) either) either )  either) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val start_happy3 : ( ( CTranslUnit, (CExtDecl, (CStat, (CExpr, unit) either) either) either )  either) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val start_happy4 : ( ( CTranslUnit, (CExtDecl, (CStat, (CExpr, unit) either) either) either )  either) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val translation_unit : (CTranslUnit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val ext_decl_list1 : ( ( CExtDecl list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val ext_decl_list2 : ( ( CExtDecl list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val ext_decl_list3 : ( ( CExtDecl list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val external_declaration1 : (CExtDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val external_declaration2 : (CExtDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val external_declaration3 : (CExtDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val external_declaration4 : (CExtDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val function_definition1 : (CFunDef) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val function_definition2 : (CFunDef) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val function_definition3 : (CFunDef) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val function_definition4 : (CFunDef) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val function_definition5 : (CFunDef) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val function_definition6 : (CFunDef) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val function_definition7 : (CFunDef) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val function_definition8 : (CFunDef) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val function_definition9 : (CFunDef) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val function_definition10 : (CFunDef) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val function_definition11 : (CFunDef) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val function_definition12 : (CFunDef) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val function_definition13 : (CFunDef) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val function_definition14 : (CFunDef) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val function_declarator : (CDeclr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val statement1 : (CStat) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val statement2 : (CStat) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val statement3 : (CStat) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val statement4 : (CStat) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val statement5 : (CStat) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val statement6 : (CStat) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val statement7 : (CStat) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val labeled_statement1 : (CStat) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val labeled_statement2 : (CStat) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val labeled_statement3 : (CStat) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val labeled_statement4 : (CStat) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val compound_statement1 : (CStat) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val compound_statement2 : (CStat) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val enter_scope : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val leave_scope : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val block_item_list1 : ( ( CBlockItem list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val block_item_list2 : ( ( CBlockItem list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val block_item1 : (CBlockItem) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val block_item2 : (CBlockItem) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val nested_declaration1 : (CBlockItem) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val nested_declaration2 : (CBlockItem) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val nested_declaration3 : (CBlockItem) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val nested_function_definition1 : (CFunDef) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val nested_function_definition2 : (CFunDef) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val nested_function_definition3 : (CFunDef) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val nested_function_definition4 : (CFunDef) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val nested_function_definition5 : (CFunDef) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val label_declarations1 : ( ( Ident list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val label_declarations2 : ( ( Ident list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val expression_statement1 : (CStat) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val expression_statement2 : (CStat) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val selection_statement1 : (CStat) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val selection_statement2 : (CStat) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val selection_statement3 : (CStat) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val iteration_statement1 : (CStat) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val iteration_statement2 : (CStat) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val iteration_statement3 : (CStat) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val iteration_statement4 : (CStat) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val jump_statement1 : (CStat) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val jump_statement2 : (CStat) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val jump_statement3 : (CStat) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val jump_statement4 : (CStat) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val jump_statement5 : (CStat) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val asm_statement1 : (CAsmStmt) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val asm_statement2 : (CAsmStmt) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val asm_statement3 : (CAsmStmt) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val asm_statement4 : (CAsmStmt) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val maybe_type_qualifier1 : (CTypeQual Maybe) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val maybe_type_qualifier2 : (CTypeQual Maybe) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val asm_operands1 : (CAsmOperand list) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val asm_operands2 : (CAsmOperand list) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val nonnull_asm_operands1 : ( ( CAsmOperand list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val nonnull_asm_operands2 : ( ( CAsmOperand list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val asm_operand1 : (CAsmOperand) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val asm_operand2 : (CAsmOperand) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val asm_operand3 : (CAsmOperand) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val asm_clobbers1 : ( ( CStrLit list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val asm_clobbers2 : ( ( CStrLit list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declaration1 : (CDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declaration2 : (CDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declaration3 : (CDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declaration4 : (CDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declaration5 : (CDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declaration_list1 : ( ( CDecl list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declaration_list2 : ( ( CDecl list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val default_declaring_list1 : (CDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val default_declaring_list2 : (CDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val default_declaring_list3 : (CDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val default_declaring_list4 : (CDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val default_declaring_list5 : (CDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val asm_attrs_opt : ( ( CStrLit Maybe * CAttr list ) ) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declaring_list1 : (CDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declaring_list2 : (CDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declaring_list3 : (CDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declaration_specifier1 : (CDeclSpec list) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declaration_specifier2 : (CDeclSpec list) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declaration_specifier3 : (CDeclSpec list) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declaration_qualifier_list1 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declaration_qualifier_list2 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declaration_qualifier_list3 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declaration_qualifier_list4 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declaration_qualifier_list5 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declaration_qualifier_list6 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declaration_qualifier1 : (CDeclSpec) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declaration_qualifier2 : (CDeclSpec) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declaration_qualifier3 : (CDeclSpec) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declaration_qualifier4 : (CDeclSpec) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declaration_qualifier_without_types1 : (CDeclSpec) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declaration_qualifier_without_types2 : (CDeclSpec) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declaration_qualifier_without_types3 : (CDeclSpec) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val storage_class1 : (CStorageSpec) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val storage_class2 : (CStorageSpec) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val storage_class3 : (CStorageSpec) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val storage_class4 : (CStorageSpec) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val storage_class5 : (CStorageSpec) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val storage_class6 : (CStorageSpec) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val function_specifier1 : (CFunSpec) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val function_specifier2 : (CFunSpec) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val alignment_specifier1 : (CAlignSpec) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val alignment_specifier2 : (CAlignSpec) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val type_specifier1 : (CDeclSpec list) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val type_specifier2 : (CDeclSpec list) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val type_specifier3 : (CDeclSpec list) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val basic_type_name1 : (CTypeSpec) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val basic_type_name2 : (CTypeSpec) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val basic_type_name3 : (CTypeSpec) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val basic_type_name4 : (CTypeSpec) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val basic_type_name5 : (CTypeSpec) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val basic_type_name6 : (CTypeSpec) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val basic_type_name7 : (CTypeSpec) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val basic_type_name8 : (CTypeSpec) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val basic_type_name9 : (CTypeSpec) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val basic_type_name10 : (CTypeSpec) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val basic_type_name11 : (CTypeSpec) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val basic_type_name12 : (CTypeSpec) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val basic_declaration_specifier1 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val basic_declaration_specifier2 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val basic_declaration_specifier3 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val basic_declaration_specifier4 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val basic_declaration_specifier5 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val basic_type_specifier1 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val basic_type_specifier2 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val basic_type_specifier3 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val basic_type_specifier4 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val basic_type_specifier5 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val basic_type_specifier6 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val basic_type_specifier7 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val sue_declaration_specifier1 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val sue_declaration_specifier2 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val sue_declaration_specifier3 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val sue_declaration_specifier4 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val sue_type_specifier1 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val sue_type_specifier2 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val sue_type_specifier3 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val sue_type_specifier4 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val sue_type_specifier5 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val sue_type_specifier6 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val typedef_declaration_specifier1 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val typedef_declaration_specifier2 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val typedef_declaration_specifier3 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val typedef_declaration_specifier4 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val typedef_declaration_specifier5 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val typedef_declaration_specifier6 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val typedef_type_specifier1 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val typedef_type_specifier2 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val typedef_type_specifier3 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val typedef_type_specifier4 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val typedef_type_specifier5 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val typedef_type_specifier6 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val typedef_type_specifier7 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val typedef_type_specifier8 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val typedef_type_specifier9 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val typedef_type_specifier10 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val typedef_type_specifier11 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val typedef_type_specifier12 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val typedef_type_specifier13 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val typedef_type_specifier14 : ( ( CDeclSpec list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val elaborated_type_name1 : (CTypeSpec) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val elaborated_type_name2 : (CTypeSpec) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val struct_or_union_specifier1 : (CStructUnion) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val struct_or_union_specifier2 : (CStructUnion) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val struct_or_union_specifier3 : (CStructUnion) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val struct_or_union1 : (CStructTag Located) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val struct_or_union2 : (CStructTag Located) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val struct_declaration_list1 : ( ( CDecl list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val struct_declaration_list2 : ( ( CDecl list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val struct_declaration_list3 : ( ( CDecl list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val struct_declaration1 : (CDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val struct_declaration2 : (CDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val struct_declaration3 : (CDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val struct_default_declaring_list1 : (CDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val struct_default_declaring_list2 : (CDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val struct_default_declaring_list3 : (CDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val struct_declaring_list1 : (CDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val struct_declaring_list2 : (CDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val struct_declaring_list3 : (CDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val struct_declarator1 : ( ( CDeclr Maybe * CExpr Maybe ) ) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val struct_declarator2 : ( ( CDeclr Maybe * CExpr Maybe ) ) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val struct_declarator3 : ( ( CDeclr Maybe * CExpr Maybe ) ) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val struct_identifier_declarator1 : ( ( CDeclr Maybe * CExpr Maybe ) ) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val struct_identifier_declarator2 : ( ( CDeclr Maybe * CExpr Maybe ) ) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val struct_identifier_declarator3 : ( ( CDeclr Maybe * CExpr Maybe ) ) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val struct_identifier_declarator4 : ( ( CDeclr Maybe * CExpr Maybe ) ) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val enum_specifier1 : (CEnum) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val enum_specifier2 : (CEnum) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val enum_specifier3 : (CEnum) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val enum_specifier4 : (CEnum) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val enum_specifier5 : (CEnum) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val enumerator_list1 : ( ( ((Ident * CExpr Maybe)) list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val enumerator_list2 : ( ( ((Ident * CExpr Maybe)) list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val enumerator1 : ( ( Ident * CExpr Maybe ) ) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val enumerator2 : ( ( Ident * CExpr Maybe ) ) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val enumerator3 : ( ( Ident * CExpr Maybe ) ) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val enumerator4 : ( ( Ident * CExpr Maybe ) ) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val type_qualifier1 : (CTypeQual) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val type_qualifier2 : (CTypeQual) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val type_qualifier3 : (CTypeQual) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val type_qualifier4 : (CTypeQual) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val type_qualifier5 : (CTypeQual) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val type_qualifier6 : (CTypeQual) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val type_qualifier_list1 : ( ( CTypeQual list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val type_qualifier_list2 : ( ( CTypeQual list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val type_qualifier_list3 : ( ( CTypeQual list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declarator1 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declarator2 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val asm_opt1 : (CStrLit Maybe) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val asm_opt2 : (CStrLit Maybe) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val typedef_declarator1 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val typedef_declarator2 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val parameter_typedef_declarator1 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val parameter_typedef_declarator2 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val parameter_typedef_declarator3 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val clean_typedef_declarator1 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val clean_typedef_declarator2 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val clean_typedef_declarator3 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val clean_typedef_declarator4 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val clean_typedef_declarator5 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val clean_postfix_typedef_declarator1 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val clean_postfix_typedef_declarator2 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val clean_postfix_typedef_declarator3 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val clean_postfix_typedef_declarator4 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val paren_typedef_declarator1 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val paren_typedef_declarator2 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val paren_typedef_declarator3 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val paren_typedef_declarator4 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val paren_typedef_declarator5 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val paren_typedef_declarator6 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val paren_typedef_declarator7 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val paren_postfix_typedef_declarator1 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val paren_postfix_typedef_declarator2 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val paren_postfix_typedef_declarator3 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val simple_paren_typedef_declarator1 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val simple_paren_typedef_declarator2 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val identifier_declarator1 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val identifier_declarator2 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val unary_identifier_declarator1 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val unary_identifier_declarator2 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val unary_identifier_declarator3 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val unary_identifier_declarator4 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val unary_identifier_declarator5 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_identifier_declarator1 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_identifier_declarator2 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_identifier_declarator3 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_identifier_declarator4 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_identifier_declarator5 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val paren_identifier_declarator1 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val paren_identifier_declarator2 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val paren_identifier_declarator3 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val function_declarator_old : (CDeclr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val old_function_declarator1 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val old_function_declarator2 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val old_function_declarator3 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_old_function_declarator1 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_old_function_declarator2 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_old_function_declarator3 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val parameter_type_list1 : ( ( CDecl list * Bool ) ) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val parameter_type_list2 : ( ( CDecl list * Bool ) ) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val parameter_type_list3 : ( ( CDecl list * Bool ) ) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val parameter_list1 : ( ( CDecl list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val parameter_list2 : ( ( CDecl list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val parameter_declaration1 : (CDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val parameter_declaration2 : (CDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val parameter_declaration3 : (CDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val parameter_declaration4 : (CDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val parameter_declaration5 : (CDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val parameter_declaration6 : (CDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val parameter_declaration7 : (CDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val parameter_declaration8 : (CDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val parameter_declaration9 : (CDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val parameter_declaration10 : (CDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val parameter_declaration11 : (CDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val parameter_declaration12 : (CDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val parameter_declaration13 : (CDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val parameter_declaration14 : (CDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val parameter_declaration15 : (CDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val identifier_list1 : ( ( Ident list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val identifier_list2 : ( ( Ident list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val type_name1 : (CDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val type_name2 : (CDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val type_name3 : (CDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val type_name4 : (CDecl) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val abstract_declarator1 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val abstract_declarator2 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val abstract_declarator3 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfixing_abstract_declarator1 : ( ( CDeclrR -> CDeclrR ) ) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfixing_abstract_declarator2 : ( ( CDeclrR -> CDeclrR ) ) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val array_abstract_declarator1 : ( ( CDeclrR -> CDeclrR ) ) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val array_abstract_declarator2 : ( ( CDeclrR -> CDeclrR ) ) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_array_abstract_declarator1 : ( ( CDeclrR -> CDeclrR ) ) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_array_abstract_declarator2 : ( ( CDeclrR -> CDeclrR ) ) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_array_abstract_declarator3 : ( ( CDeclrR -> CDeclrR ) ) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_array_abstract_declarator4 : ( ( CDeclrR -> CDeclrR ) ) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_array_abstract_declarator5 : ( ( CDeclrR -> CDeclrR ) ) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_array_abstract_declarator6 : ( ( CDeclrR -> CDeclrR ) ) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_array_abstract_declarator7 : ( ( CDeclrR -> CDeclrR ) ) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_array_abstract_declarator8 : ( ( CDeclrR -> CDeclrR ) ) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_array_abstract_declarator9 : ( ( CDeclrR -> CDeclrR ) ) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_array_abstract_declarator10 : ( ( CDeclrR -> CDeclrR ) ) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_array_abstract_declarator11 : ( ( CDeclrR -> CDeclrR ) ) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val unary_abstract_declarator1 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val unary_abstract_declarator2 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val unary_abstract_declarator3 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val unary_abstract_declarator4 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val unary_abstract_declarator5 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val unary_abstract_declarator6 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_abstract_declarator1 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_abstract_declarator2 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_abstract_declarator3 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_abstract_declarator4 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_abstract_declarator5 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_abstract_declarator6 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_abstract_declarator7 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_abstract_declarator8 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_abstract_declarator9 : (CDeclrR) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val initializer1 : (CInit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val initializer2 : (CInit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val initializer3 : (CInit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val initializer_opt1 : (CInit Maybe) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val initializer_opt2 : (CInit Maybe) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val initializer_list1 : (CInitList Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val initializer_list2 : (CInitList Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val initializer_list3 : (CInitList Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val initializer_list4 : (CInitList Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val initializer_list5 : (CInitList Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val designation1 : (CDesignator list) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val designation2 : (CDesignator list) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val designation3 : (CDesignator list) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val designator_list1 : ( ( CDesignator list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val designator_list2 : ( ( CDesignator list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val designator1 : (CDesignator) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val designator2 : (CDesignator) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val designator3 : (CDesignator) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val array_designator : (CDesignator) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val primary_expression1 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val primary_expression2 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val primary_expression3 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val primary_expression4 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val primary_expression5 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val primary_expression6 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val primary_expression7 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val primary_expression8 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val primary_expression9 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val generic_assoc_list1 : ( ( ((CDecl Maybe * CExpr)) list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val generic_assoc_list2 : ( ( ((CDecl Maybe * CExpr)) list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val generic_assoc1 : ( ( CDecl Maybe * CExpr ) ) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val generic_assoc2 : ( ( CDecl Maybe * CExpr ) ) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val offsetof_member_designator1 : ( ( CDesignator list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val offsetof_member_designator2 : ( ( CDesignator list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val offsetof_member_designator3 : ( ( CDesignator list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_expression1 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_expression2 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_expression3 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_expression4 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_expression5 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_expression6 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_expression7 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_expression8 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_expression9 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_expression10 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val argument_expression_list1 : ( ( CExpr list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val argument_expression_list2 : ( ( CExpr list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val unary_expression1 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val unary_expression2 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val unary_expression3 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val unary_expression4 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val unary_expression5 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val unary_expression6 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val unary_expression7 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val unary_expression8 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val unary_expression9 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val unary_expression10 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val unary_expression11 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val unary_expression12 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val unary_operator1 : (CUnaryOp Located) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val unary_operator2 : (CUnaryOp Located) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val unary_operator3 : (CUnaryOp Located) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val unary_operator4 : (CUnaryOp Located) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val unary_operator5 : (CUnaryOp Located) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val unary_operator6 : (CUnaryOp Located) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val cast_expression1 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val cast_expression2 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val multiplicative_expression1 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val multiplicative_expression2 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val multiplicative_expression3 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val multiplicative_expression4 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val additive_expression1 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val additive_expression2 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val additive_expression3 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val shift_expression1 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val shift_expression2 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val shift_expression3 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val relational_expression1 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val relational_expression2 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val relational_expression3 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val relational_expression4 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val relational_expression5 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val equality_expression1 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val equality_expression2 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val equality_expression3 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val and_expression1 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val and_expression2 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val exclusive_or_expression1 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val exclusive_or_expression2 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val inclusive_or_expression1 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val inclusive_or_expression2 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val logical_and_expression1 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val logical_and_expression2 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val logical_or_expression1 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val logical_or_expression2 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val conditional_expression1 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val conditional_expression2 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val conditional_expression3 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val assignment_expression1 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val assignment_expression2 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val assignment_operator1 : (CAssignOp Located) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val assignment_operator2 : (CAssignOp Located) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val assignment_operator3 : (CAssignOp Located) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val assignment_operator4 : (CAssignOp Located) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val assignment_operator5 : (CAssignOp Located) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val assignment_operator6 : (CAssignOp Located) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val assignment_operator7 : (CAssignOp Located) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val assignment_operator8 : (CAssignOp Located) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val assignment_operator9 : (CAssignOp Located) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val assignment_operator10 : (CAssignOp Located) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val assignment_operator11 : (CAssignOp Located) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val expression1 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val expression2 : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val comma_expression1 : ( ( CExpr list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val comma_expression2 : ( ( CExpr list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val expression_opt1 : (CExpr Maybe) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val expression_opt2 : (CExpr Maybe) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val assignment_expression_opt1 : (CExpr Maybe) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val assignment_expression_opt2 : (CExpr Maybe) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val constant_expression : (CExpr) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val constant1 : (CConst) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val constant2 : (CConst) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val constant3 : (CConst) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val string_literal1 : (CStrLit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val string_literal2 : (CStrLit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val string_literal_list1 : ( ( CString list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val string_literal_list2 : ( ( CString list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val clang_version_literal : (ClangCVersion) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val identifier1 : (Ident) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val identifier2 : (Ident) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val attrs_opt1 : (CAttr list) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val attrs_opt2 : (CAttr list) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val attrs1 : (CAttr list) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val attrs2 : (CAttr list) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val attr : (CAttr list) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val attribute_list1 : ( ( CAttr list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val attribute_list2 : ( ( CAttr list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val attribute1 : (CAttr Maybe) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val attribute2 : (CAttr Maybe) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val attribute3 : (CAttr Maybe) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val attribute4 : (CAttr Maybe) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val attribute5 : (CAttr Maybe) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val attribute_params1 : ( ( CExpr list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val attribute_params2 : ( ( CExpr list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val attribute_params3 : ( ( CExpr list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val attribute_params4 : ( ( CExpr list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val attribute_params5 : ( ( CExpr list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val attribute_params6 : ( ( CExpr list )  Reversed) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
end
signature C_Grammar_TOKENS =
sig
type ('a,'b) token
type arg
type svalue0
type svalue = arg -> svalue0 * arg
val x25_eof:  'a * 'a -> (svalue,'a) token
val clangcversion: (C_Ast.ClangCVersion) *  'a * 'a -> (svalue,'a) token
val x5f_x5f_builtin_types_compatible_p: (string) *  'a * 'a -> (svalue,'a) token
val x5f_x5f_builtin_offsetof: (string) *  'a * 'a -> (svalue,'a) token
val x5f_x5f_builtin_va_arg: (string) *  'a * 'a -> (svalue,'a) token
val x5f_x5f_imag_x5f_x5f: (string) *  'a * 'a -> (svalue,'a) token
val x5f_x5f_real_x5f_x5f: (string) *  'a * 'a -> (svalue,'a) token
val x5f_x5f_extension_x5f_x5f: (string) *  'a * 'a -> (svalue,'a) token
val x5f_x5f_attribute_x5f_x5f: (string) *  'a * 'a -> (svalue,'a) token
val tyident: (C_Ast.ident) *  'a * 'a -> (svalue,'a) token
val ident: (C_Ast.ident) *  'a * 'a -> (svalue,'a) token
val cstr: (C_Ast.cString) *  'a * 'a -> (svalue,'a) token
val cfloat: (C_Ast.cFloat) *  'a * 'a -> (svalue,'a) token
val cint: (C_Ast.cInteger) *  'a * 'a -> (svalue,'a) token
val cchar: (C_Ast.cChar) *  'a * 'a -> (svalue,'a) token
val while0: (string) *  'a * 'a -> (svalue,'a) token
val volatile: (string) *  'a * 'a -> (svalue,'a) token
val void: (string) *  'a * 'a -> (svalue,'a) token
val unsigned: (string) *  'a * 'a -> (svalue,'a) token
val union: (string) *  'a * 'a -> (svalue,'a) token
val x5f_x5f_thread: (string) *  'a * 'a -> (svalue,'a) token
val typeof: (string) *  'a * 'a -> (svalue,'a) token
val typedef: (string) *  'a * 'a -> (svalue,'a) token
val switch: (string) *  'a * 'a -> (svalue,'a) token
val struct0: (string) *  'a * 'a -> (svalue,'a) token
val x5f_Static_assert: (string) *  'a * 'a -> (svalue,'a) token
val static: (string) *  'a * 'a -> (svalue,'a) token
val sizeof: (string) *  'a * 'a -> (svalue,'a) token
val signed: (string) *  'a * 'a -> (svalue,'a) token
val short: (string) *  'a * 'a -> (svalue,'a) token
val return0: (string) *  'a * 'a -> (svalue,'a) token
val restrict: (string) *  'a * 'a -> (svalue,'a) token
val register: (string) *  'a * 'a -> (svalue,'a) token
val x5f_Nonnull: (string) *  'a * 'a -> (svalue,'a) token
val x5f_Nullable: (string) *  'a * 'a -> (svalue,'a) token
val x5f_Noreturn: (string) *  'a * 'a -> (svalue,'a) token
val x5f_x5f_label_x5f_x5f: (string) *  'a * 'a -> (svalue,'a) token
val long: (string) *  'a * 'a -> (svalue,'a) token
val x5f_x5f_int_x31_x32_x38: (string) *  'a * 'a -> (svalue,'a) token
val int: (string) *  'a * 'a -> (svalue,'a) token
val inline: (string) *  'a * 'a -> (svalue,'a) token
val if0: (string) *  'a * 'a -> (svalue,'a) token
val goto: (string) *  'a * 'a -> (svalue,'a) token
val x5f_Generic: (string) *  'a * 'a -> (svalue,'a) token
val for0: (string) *  'a * 'a -> (svalue,'a) token
val float: (string) *  'a * 'a -> (svalue,'a) token
val extern: (string) *  'a * 'a -> (svalue,'a) token
val enum: (string) *  'a * 'a -> (svalue,'a) token
val else0: (string) *  'a * 'a -> (svalue,'a) token
val double: (string) *  'a * 'a -> (svalue,'a) token
val do0: (string) *  'a * 'a -> (svalue,'a) token
val default: (string) *  'a * 'a -> (svalue,'a) token
val x5f_Complex: (string) *  'a * 'a -> (svalue,'a) token
val continue: (string) *  'a * 'a -> (svalue,'a) token
val const: (string) *  'a * 'a -> (svalue,'a) token
val char: (string) *  'a * 'a -> (svalue,'a) token
val case0: (string) *  'a * 'a -> (svalue,'a) token
val x5f_Bool: (string) *  'a * 'a -> (svalue,'a) token
val break: (string) *  'a * 'a -> (svalue,'a) token
val auto: (string) *  'a * 'a -> (svalue,'a) token
val asm: (string) *  'a * 'a -> (svalue,'a) token
val x5f_Atomic: (string) *  'a * 'a -> (svalue,'a) token
val alignas: (string) *  'a * 'a -> (svalue,'a) token
val alignof: (string) *  'a * 'a -> (svalue,'a) token
val x2e_x2e_x2e: (string) *  'a * 'a -> (svalue,'a) token
val x7d: (string) *  'a * 'a -> (svalue,'a) token
val x7b: (string) *  'a * 'a -> (svalue,'a) token
val x3b: (string) *  'a * 'a -> (svalue,'a) token
val x2c: (string) *  'a * 'a -> (svalue,'a) token
val x3e_x3e_x3d: (string) *  'a * 'a -> (svalue,'a) token
val x3c_x3c_x3d: (string) *  'a * 'a -> (svalue,'a) token
val x7c_x3d: (string) *  'a * 'a -> (svalue,'a) token
val x5e_x3d: (string) *  'a * 'a -> (svalue,'a) token
val x26_x3d: (string) *  'a * 'a -> (svalue,'a) token
val x25_x3d: (string) *  'a * 'a -> (svalue,'a) token
val x2f_x3d: (string) *  'a * 'a -> (svalue,'a) token
val x2a_x3d: (string) *  'a * 'a -> (svalue,'a) token
val x2d_x3d: (string) *  'a * 'a -> (svalue,'a) token
val x2b_x3d: (string) *  'a * 'a -> (svalue,'a) token
val x3d: (string) *  'a * 'a -> (svalue,'a) token
val x3a: (string) *  'a * 'a -> (svalue,'a) token
val x3f: (string) *  'a * 'a -> (svalue,'a) token
val x7c_x7c: (string) *  'a * 'a -> (svalue,'a) token
val x26_x26: (string) *  'a * 'a -> (svalue,'a) token
val x7c: (string) *  'a * 'a -> (svalue,'a) token
val x5e: (string) *  'a * 'a -> (svalue,'a) token
val x21_x3d: (string) *  'a * 'a -> (svalue,'a) token
val x3d_x3d: (string) *  'a * 'a -> (svalue,'a) token
val x3e_x3d: (string) *  'a * 'a -> (svalue,'a) token
val x3e: (string) *  'a * 'a -> (svalue,'a) token
val x3c_x3d: (string) *  'a * 'a -> (svalue,'a) token
val x3c: (string) *  'a * 'a -> (svalue,'a) token
val x3e_x3e: (string) *  'a * 'a -> (svalue,'a) token
val x3c_x3c: (string) *  'a * 'a -> (svalue,'a) token
val x26: (string) *  'a * 'a -> (svalue,'a) token
val x25: (string) *  'a * 'a -> (svalue,'a) token
val x2f: (string) *  'a * 'a -> (svalue,'a) token
val x2a: (string) *  'a * 'a -> (svalue,'a) token
val x2d: (string) *  'a * 'a -> (svalue,'a) token
val x2b: (string) *  'a * 'a -> (svalue,'a) token
val x2d_x2d: (string) *  'a * 'a -> (svalue,'a) token
val x2b_x2b: (string) *  'a * 'a -> (svalue,'a) token
val x7e: (string) *  'a * 'a -> (svalue,'a) token
val x21: (string) *  'a * 'a -> (svalue,'a) token
val x2e: (string) *  'a * 'a -> (svalue,'a) token
val x2d_x3e: (string) *  'a * 'a -> (svalue,'a) token
val x5d: (string) *  'a * 'a -> (svalue,'a) token
val x5b: (string) *  'a * 'a -> (svalue,'a) token
val x29: (string) *  'a * 'a -> (svalue,'a) token
val x28: (string) *  'a * 'a -> (svalue,'a) token
val error:  'a * 'a -> (svalue,'a) token
val start_expression:  'a * 'a -> (svalue,'a) token
val start_statement:  'a * 'a -> (svalue,'a) token
val start_external_declaration:  'a * 'a -> (svalue,'a) token
val start_translation_unit:  'a * 'a -> (svalue,'a) token
end
signature C_Grammar_LRVALS=
sig
structure Tokens : C_Grammar_TOKENS
structure ParserData:PARSER_DATA1
sharing type ParserData.Token.token = Tokens.token
end
