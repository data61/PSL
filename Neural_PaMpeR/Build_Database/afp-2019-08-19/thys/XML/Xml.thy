(* Title:     Xml
   Author:    Christian Sternagel
   Author:    René Thiemann
*)

section \<open>Parsing and Printing XML Documents\<close>

theory Xml
imports
  Certification_Monads.Parser_Monad
  "HOL-Library.Char_ord"
begin

datatype xml =
  \<comment> \<open>node-name, attributes, child-nodes\<close>
  XML string "(string \<times> string) list" "xml list" |
  XML_text string

datatype xmldoc =
  \<comment> \<open>header, body\<close>
  XMLDOC "string list" (root_node: xml)

fun tag :: "xml \<Rightarrow> string" where
  "tag (XML name _ _ ) = name" |
  "tag (XML_text _) = []"
hide_const (open) tag

fun children :: "xml \<Rightarrow> xml list" where
  "children (XML _ _ cs) = cs" |
  "children (XML_text _) = []"
hide_const (open) children

fun num_children :: "xml \<Rightarrow> nat" where
  "num_children (XML _ _ cs) = length cs" |
  "num_children (XML_text _) = 0"
hide_const (open) num_children


subsection \<open>Printing of XML Nodes and Documents\<close>

instantiation xml :: "show"
begin

definition shows_attr :: "string \<times> string \<Rightarrow> shows"
where
  "shows_attr av = shows (fst av) o shows_string (''=\"'' @ snd av @ ''\"'')"

definition shows_attrs :: "(string \<times> string) list \<Rightarrow> shows"
where
  "shows_attrs as = foldr (\<lambda>a. '' '' +#+ shows_attr a) as"

fun shows_XML_indent :: "string \<Rightarrow> nat \<Rightarrow> xml \<Rightarrow> shows"
where
  "shows_XML_indent ind i (XML n a c) =
    (''\<newline>'' +#+ ind +#+ ''<'' +#+ shows n +@+ shows_attrs a +@+
      (if c = [] then shows_string ''/>''
      else (
        ''>'' +#+
          foldr (shows_XML_indent (replicate i (CHR '' '') @ ind) i) c +@+ ''\<newline>'' +#+ ind +#+
        ''</'' +#+ shows n +@+ shows_string ''>'')))" |
  "shows_XML_indent ind i (XML_text t) = shows_string t"

definition "shows_prec (d::nat) xml = shows_XML_indent '''' 2 xml"

definition "shows_list (xs :: xml list) = showsp_list shows_prec 0 xs"

lemma shows_attr_append:
  "(s +#+ shows_attr av) (r @ t) = (s +#+ shows_attr av) r @ t"
  unfolding shows_attr_def by (cases av) (auto simp: show_law_simps)

lemma shows_attrs_append [show_law_simps]:
  "shows_attrs as (r @ s) = shows_attrs as r @ s"
  using shows_attr_append by (induct as) (simp_all add: shows_attrs_def)

lemma append_xml':
  "shows_XML_indent ind i xml (r @ s) = shows_XML_indent ind i xml r @ s"
  by (induct xml arbitrary: ind r s) (auto simp: show_law_simps)

lemma shows_prec_xml_append [show_law_simps]:
  "shows_prec d (xml::xml) (r @ s) = shows_prec d xml r @ s"
  unfolding shows_prec_xml_def by (rule append_xml')

instance
  by standard (simp_all add: show_law_simps shows_list_xml_def)

end

instantiation xmldoc :: "show"
begin

fun shows_xmldoc
where
  "shows_xmldoc (XMLDOC h x) = shows_lines h o shows_nl o shows x"

definition "shows_prec (d::nat) doc = shows_xmldoc doc"
definition "shows_list (xs :: xmldoc list) = showsp_list shows_prec 0 xs"

lemma shows_prec_xmldoc_append [show_law_simps]:
  "shows_prec d (x::xmldoc) (r @ s) = shows_prec d x r @ s"
  by (cases x) (auto simp: shows_prec_xmldoc_def show_law_simps)

instance
  by standard (simp_all add: show_law_simps shows_list_xmldoc_def)

end


subsection \<open>XML-Parsing\<close>

definition parse_text :: "string option parser"
where
  "parse_text = do {
    ts \<leftarrow> many ((\<noteq>) CHR ''<'');
    let text = trim ts;
    if text = [] then return None
    else return (Some (List.rev (trim (List.rev text))))
  }"

lemma is_parser_parse_text [intro]:
  "is_parser parse_text"
  by (auto simp: parse_text_def)

lemma parse_text_consumes:
  assumes *: "ts \<noteq> []" "hd ts \<noteq> CHR ''<''"
    and parse: "parse_text ts = Inr (t, ts')"
  shows "length ts' < length ts"
proof -
  from * obtain a tss where ts: "ts = a # tss" and not: "a \<noteq> CHR ''<''" 
    by (cases ts, auto)
  note parse = parse [unfolded parse_text_def Let_def ts]
  from parse obtain x1 x2 where many: "many ((\<noteq>) CHR ''<'') tss = Inr (x1, x2)"
    using not by (cases "many ((\<noteq>) CHR ''<'') tss", 
      auto simp: bind_def)
  from is_parser_many many have len: "length x2 \<le> length tss" by blast
  from parse many have "length ts' \<le> length x2"
    using not by (simp add: bind_def return_def split: if_splits)
  with len show ?thesis unfolding ts by auto
qed

definition parse_attribute_value :: "string parser"
where
  "parse_attribute_value = do {
    exactly [CHR ''\"''];
    v \<leftarrow> many ((\<noteq>) CHR ''\"'');
    exactly [CHR ''\"''];
    return v
  }"

lemma is_parser_parse_attribute_value [intro]:
  "is_parser parse_attribute_value"
  by (auto simp: parse_attribute_value_def)

text \<open>A list of characters that are considered to be "letters" for tag-names.\<close>
definition letters :: "char list"
where
  "letters = ''abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_0123456789&;:-''"

definition is_letter :: "char \<Rightarrow> bool"
where
  "is_letter c \<longleftrightarrow> c \<in> set letters"

lemma is_letter_code [code]:
  "is_letter c \<longleftrightarrow>
    CHR ''a'' \<le> c \<and> c \<le> CHR ''z'' \<or>
    CHR ''A'' \<le> c \<and> c \<le> CHR ''Z'' \<or>
    CHR ''0'' \<le> c \<and> c \<le> CHR ''9'' \<or>
    c \<in> set ''_&;:-''"
  by (cases c) (simp add: is_letter_def letters_def)

definition many_letters :: "string parser"
where
  [simp]: "many_letters = manyof letters"

lemma many_letters [code, code_unfold]:
  "many_letters = many is_letter"
  by (simp add: is_letter_def [abs_def] manyof_def)

definition parse_name :: "string parser"
where
  "parse_name s = (do {
    n \<leftarrow> many_letters;
    spaces;
    if n = [] then
      error (''expected letter '' @ letters @ '' but first symbol is \"'' @ take 1 s @ ''\"'')
    else return n
  }) s"

lemma is_parser_parse_name [intro]:
  "is_parser parse_name"
proof 
  fix s r x
  assume res: "parse_name s = Inr (x, r)"
  let ?exp = "do {
    n \<leftarrow> many_letters;
    spaces;
    if n = [] then
      error (''expected letter '' @ letters @ '' but first symbol is \"'' @ take 1 s @ ''\"'')
    else return n
  }"
  have isp: "is_parser ?exp" by auto
  have id: "parse_name s = ?exp s" by (simp add: parse_name_def)
  from isp [unfolded is_parser_def, rule_format, OF res [unfolded id]] 
  show "length r \<le> length s" .
qed

function (sequential) parse_attributes :: "(string \<times> string) list parser"
where
  "parse_attributes [] = Error_Monad.return ([], [])" |
  "parse_attributes (c # s) =
    (if c \<in> set ''/>'' then Error_Monad.return ([], c # s)
    else (do {
      k \<leftarrow> parse_name;
      exactly ''='';
      v \<leftarrow> parse_attribute_value;
      atts \<leftarrow> parse_attributes;
      return ((k, v) # atts)
    }) (c # s))"
  by pat_completeness auto

termination parse_attributes
proof
  show "wf (measure length)" by simp
next
  fix c s y ts ya tsa yb tsb
  assume pn: "parse_name (c # s) = Inr (y, ts)"
    and oo: "exactly ''='' ts = Inr (ya, tsa)"
    and pav: "parse_attribute_value tsa = Inr (yb, tsb)"  
  have cp: "is_cparser (exactly ''='')" by auto
  from cp [unfolded is_cparser_def] oo have 1: "length ts > length tsa" by auto
  from is_parser_parse_name [unfolded is_parser_def] pn
    have 2: "length (c # s) \<ge> length ts" by force
  from is_parser_parse_attribute_value [unfolded is_parser_def] pav
    have 3: "length tsa \<ge> length tsb" by force
  from 1 2 3
    show "(tsb, c # s) \<in> measure length" 
    by auto
qed

lemma is_parser_parse_attributes [intro]:
  "is_parser parse_attributes"
proof
  fix s r x 
  assume "parse_attributes s = Inr (x, r)"
  then show "length r \<le> length s"
  proof (induct arbitrary: x rule: parse_attributes.induct)
    case (2 c s)
    show ?case
    proof (cases "c \<in> set ''/>''")
      case True
      with 2(2) show ?thesis by simp
    next
      case False
      from False 2(2) obtain y1 s1
        where pn: "parse_name (c # s) = Inr (y1, s1)"
        by (cases "parse_name (c # s)") (auto simp: bind_def)
      from False 2(2) pn obtain y2 s2
        where oo: "exactly ''='' s1 = Inr (y2, s2)"
        by (cases "exactly ''='' s1") (auto simp: bind_def)
      from False 2(2) pn oo obtain y3 s3
        where pav: "parse_attribute_value s2 = Inr (y3, s3)"
        by (cases "parse_attribute_value s2") (auto simp: bind_def)
      from False 2(2) pn oo pav obtain y4
        where patts: "parse_attributes s3 = Inr (y4, r)"
        by (cases "parse_attributes s3") (auto simp: return_def bind_def)
      have "length r \<le> length s3" using 2(1)[OF False pn oo pav patts] .
      also have "\<dots> \<le> length s2"
        using is_parser_parse_attribute_value [unfolded is_parser_def] pav by auto
      also have "\<dots> \<le> length s1" using is_parser_exactly [unfolded is_parser_def] oo by auto
      also have "\<dots> \<le> length (c # s)"
        using is_parser_parse_name [unfolded is_parser_def] pn by force
      finally show "length r \<le> length (c # s)" by auto
    qed
  qed simp
qed

context notes [[function_internals]]
begin

function parse_nodes :: "xml list parser"
where
  "parse_nodes ts = 
    (if ts = [] \<or> take 2 ts = ''</'' then return [] ts
    else if hd ts \<noteq> CHR ''<'' then (do {
      t \<leftarrow> parse_text;
      ns \<leftarrow> parse_nodes;
      return (XML_text (the t) # ns)
    }) ts
    else (do {
      exactly ''<'';
      n \<leftarrow> parse_name;
      atts \<leftarrow> parse_attributes;
      e \<leftarrow> oneof [''/>'', ''>''];
      (\<lambda> ts'.
        if e = ''/>'' then (do {
          cs \<leftarrow> parse_nodes;
          return (XML n atts [] # cs)
        }) ts' else (do {
          cs \<leftarrow> parse_nodes;
          exactly ''</'';
          exactly n;
          exactly ''>'';
          ns \<leftarrow> parse_nodes;
          return (XML n atts cs # ns)
        }) ts')
    }) ts)"
  by pat_completeness auto

end

lemma parse_nodes_help:
  "parse_nodes_dom s \<and> (\<forall> x r. parse_nodes s = Inr (x, r) \<longrightarrow> length r \<le> length s)" (is "?prop s")
proof (induct rule: wf_induct [where P = ?prop and r = "measure length"])
  fix s
  assume "\<forall> t. (t, s) \<in> measure length \<longrightarrow> ?prop t"
  then have ind1: "\<And> t. length t < length s \<Longrightarrow> parse_nodes_dom t"  
    and ind2: "\<And> t x r. length t < length s \<Longrightarrow> parse_nodes t = Inr (x,r) \<Longrightarrow> length r \<le> length t" by auto
  let ?check = "\<lambda> s. s = [] \<or> take 2 s = ''</''"
  let ?check2 = "hd s \<noteq> CHR ''<''"
  have dom: "parse_nodes_dom s"
  proof
    fix y 
    assume "parse_nodes_rel y s"
    then show "parse_nodes_dom y"
    proof
      fix ts ya tsa
      assume *: "y = tsa"  "s = ts"  "\<not> (ts = [] \<or> take 2 ts = ''</'')"
         "hd ts \<noteq> CHR ''<''" and parse: "parse_text ts = Inr (ya, tsa)"
      from parse_text_consumes[OF _ _ parse] *(3-4) have "length tsa < length ts" by auto
      with * have len: "length s > length y" by simp
      from ind1[OF this] show "parse_nodes_dom y" .
    next
      fix ts ya tsa yaa tsb yb tsc yc tsd 
      assume "y = tsd" and "s = ts" and "\<not> ?check ts"
        and "exactly ''<'' ts = Inr (ya, tsa)"
        and "parse_name tsa = Inr (yaa, tsb)"
        and "parse_attributes tsb = Inr (yb, tsc)"
        and "oneof [''/>'', ''>''] tsc = Inr (yc, tsd)"
        and "yc = ''/>''"
      then have len: "length s > length y"
        using is_cparser_exactly [of "''<''"]
        and is_parser_oneof [of "[''/>'', ''>'']"]
        and is_parser_parse_attributes
        and is_parser_parse_name
        by (auto dest!: is_parser_length is_cparser_length)
      with ind1[OF len] show "parse_nodes_dom y" by simp
    next
      fix ts ya tsa yaa tsb yb tsc yc tsd 
      assume "y = tsd" and "s = ts" and "\<not> ?check ts"
        and "exactly ''<'' ts = Inr (ya, tsa)"
        and "parse_name tsa = Inr (yaa, tsb)"
        and "parse_attributes tsb = Inr (yb, tsc)"
        and "oneof [''/>'', ''>''] tsc = Inr (yc, tsd)"
      then have len: "length s > length y"
        using is_cparser_exactly [of "''<''", simplified]
        and is_parser_oneof [of "[''/>'', ''>'']"]
        and is_parser_parse_attributes
        and is_parser_parse_name
        by (auto dest!: is_parser_length is_cparser_length)
      with ind1[OF len] show "parse_nodes_dom y" by simp
    next
      fix ts ya tsa yaa tsb yb tsc yc tse ye tsf yf tsg yg tsh yh tsi yi tsj
      assume y: "y = tsj" and "s = ts" and "\<not> ?check ts"
        and "exactly ''<'' ts = Inr (ya, tsa)"
        and "parse_name tsa = Inr (yaa, tsb)"
        and "parse_attributes tsb = Inr (yb, tsc)"
        and "oneof [''/>'', ''>''] tsc = Inr (yc, tse)"
        and rec: "parse_nodes_sumC tse = Inr (ye, tsf)" 
        and last: "exactly ''</'' tsf = Inr (yf, tsg)"
          "exactly yaa tsg = Inr (yg, tsh)"
          "exactly ''>'' tsh = Inr (yi, tsj)"
      then have len: "length s > length tse"
        using is_cparser_exactly [of "''<''", simplified]
        and is_parser_oneof [of "[''/>'', ''>'']"]
        and is_parser_parse_attributes
        and is_parser_parse_name
        by (auto dest!: is_parser_length is_cparser_length)
      from last(1) last(2) have len2a: "length tsf \<ge> length tsh"
        using is_parser_exactly [of "''</''"] and is_parser_exactly [of yaa]
        and is_parser_parse_name by (auto dest!: is_parser_length)
      have len2c: "length tsh \<ge> length y" using last(3) 
        using is_parser_exactly [of "''>''"] by (auto simp: y dest!: is_parser_length)
      from len2a len2c have len2: "length tsf \<ge> length y" by simp
      from ind2[OF len rec[unfolded parse_nodes_def[symmetric]]] len len2 have "length s > length y" by simp
      from ind1[OF this]       
      show "parse_nodes_dom y" .
    qed
  qed
  note psimps = parse_nodes.psimps[OF dom]
  show "?prop s"
  proof (intro conjI, rule dom, intro allI impI)
    fix x r    
    assume res: "parse_nodes s = Inr (x,r)"
    note res = res[unfolded psimps]
    then show "length r \<le> length s"
    proof (cases "?check s")
      case True      
      then show ?thesis using res by (simp add: return_def)
    next
      case False note oFalse = this
      show ?thesis
      proof (cases ?check2)
        case True
        note res = res[simplified False True, simplified]
        from res obtain y1 s1 where pt: "parse_text s = Inr (y1, s1)" by (cases "parse_text s", auto simp: bind_def)
        note res = res[unfolded bind_def pt, simplified]
        from res obtain y2 s2
          where pn: "parse_nodes s1 = Inr (y2, s2)"
          by (cases "parse_nodes s1") (auto simp: bind_def)
        note res = res[simplified bind_def pn, simplified]
        from res have r: "r = s2" by (simp add: return_def bind_def)
        from parse_text_consumes[OF _ True pt] False  
        have lens: "length s1 < length s" by auto
        from ind2[OF lens pn] have "length s2 \<le> length s1" .
        then show ?thesis using lens unfolding r by auto
      next
        case False note ooFalse = this
        note res = res[simplified oFalse ooFalse, simplified]
        from res obtain y1 s1 where oo: "exactly ''<'' s = Inr (y1, s1)" by (cases "exactly ''<'' s", auto simp: bind_def)
        note res = res[unfolded bind_def oo, simplified]
        from res obtain y2 s2
          where pn: "parse_name s1 = Inr (y2, s2)"
          by (cases "parse_name s1") (auto simp: bind_def psimps)
        note res = res[simplified bind_def pn, simplified]
        from res obtain y3 s3 where pa: "parse_attributes s2 = Inr (y3, s3)"
          by (cases "parse_attributes s2") (auto simp: return_def bind_def)
        note res = res[simplified pa, simplified]
        from res obtain y4 s4
          where oo2: "oneof [''/>'', ''>''] s3 = Inr (y4, s4)"
          by (cases "oneof [''/>'', ''>''] s3") (auto simp: return_def bind_def)
        note res = res[unfolded oo2, simplified]
        from is_parser_parse_attributes and is_parser_oneof [of "[''/>'', ''>'']"]
          and is_cparser_exactly [of "''<''", simplified] and is_parser_parse_name
          and oo pn pa oo2
          have s_s4: "length s > length s4"
          by (auto dest!: is_parser_length is_cparser_length)
        show ?thesis
        proof (cases "y4 = ''/>''")
          case True
          from res True obtain y5
            where pns: "parse_nodes s4 = Inr (y5, r)"
            by (cases "parse_nodes s4") (auto simp: return_def bind_def)
          from ind2[OF s_s4 pns] s_s4 show "length r \<le> length s"  by simp
        next
          case False
          note res = res[simplified False, simplified]
          from res obtain y6 s6 where pns: "parse_nodes s4 = Inr (y6, s6)"
            by (cases "parse_nodes s4") (auto simp: return_def bind_def)
          note res = res[unfolded bind_def pns, simplified, unfolded bind_def]
          from res obtain y7 s7 where oo3: "exactly ''</'' s6 = Inr (y7, s7)" by (cases "exactly ''</'' s6", auto)
          note res = res[unfolded oo3, simplified, unfolded bind_def, 
            simplified, unfolded bind_def]
          from res obtain y8 s8 where oo4: "exactly y2 s7 = Inr (y8, s8)" by (cases "exactly y2 s7", auto)
          note res = res[unfolded oo4 bind_def, simplified]
          from res obtain y10 s10 where oo5: "exactly ''>'' s8 = Inr (y10,s10)"
            by (cases "exactly ''>'' s8", auto simp: bind_def)
          note res = res[unfolded oo5 bind_def, simplified]
          from res obtain y11 s11 where pns2: "parse_nodes s10 = Inr (y11, s11)" by (cases "parse_nodes s10", auto simp: bind_def)
          note res = res[unfolded bind_def pns2, simplified]
          note one = is_parser_oneof [unfolded is_parser_def, rule_format]
          note exact = is_parser_exactly [unfolded is_parser_def, rule_format]
          from ind2[OF s_s4 pns] s_s4 exact[OF oo3] exact[OF oo4]
            have s_s7: "length s > length s8" unfolding is_parser_def by force 
          with exact[OF oo5] have s_s10: "length s > length s10" by simp
          with ind2[OF s_s10 pns2] have s_s11: "length s > length s11" by simp
          then show "length r \<le> length s" using res by (auto simp: return_def)
        qed
      qed
    qed
  qed
qed simp

termination parse_nodes using parse_nodes_help by blast

lemma parse_nodes [intro]:
  "is_parser parse_nodes" 
  unfolding is_parser_def using parse_nodes_help by blast 

text \<open>A more efficient variant of @{term "oneof [''/>'', ''>'']"}.\<close>
fun oneof_closed :: "string parser"
where
  "oneof_closed (x # xs) =
    (if x = CHR ''>'' then Error_Monad.return (''>'', trim xs)
    else if x = CHR ''/'' \<and> (case xs of [] \<Rightarrow> False | y # ys \<Rightarrow> y = CHR ''>'') then
      Error_Monad.return (''/>'', trim (tl xs))
    else err_expecting (''one of [/>, >]'') (x # xs))" |
  "oneof_closed xs = err_expecting (''one of [/>, >]'') xs"

lemma oneof_closed:
  "oneof [''/>'', ''>''] = oneof_closed" (is "?l = ?r")
proof (rule ext)
  fix xs
  have id: "''one of '' @ shows_list [''/>'', ''>''] [] = ''one of [/>, >]''"
    by (simp add: shows_list_list_def showsp_list_def pshowsp_list_def shows_list_gen_def
                  shows_string_def shows_prec_list_def shows_list_char_def)
  note d = oneof_def oneof_aux.simps id
  show "?l xs = ?r xs"
  proof (cases xs)
    case Nil
    show ?thesis unfolding Nil d by simp
  next
    case (Cons x xs) note oCons = this
    show ?thesis
    proof (cases "x = CHR ''>''")
      case True
      show ?thesis unfolding Cons d True by simp
    next
      case False note oFalse = this
      show ?thesis
      proof (cases "x = CHR ''/''")
        case False
        show ?thesis unfolding Cons d using False oFalse by simp
      next
        case True
        show ?thesis
        proof (cases xs)
          case Nil
          show ?thesis unfolding Cons Nil d by auto
        next
          case (Cons y ys)
          show ?thesis unfolding oCons Cons d by simp
        qed
      qed
    qed
  qed
qed

lemma If_removal:
  "(\<lambda> e x. if b e then f e x else g e x) = (\<lambda> e. if b e then f e else g e)"
  by (intro ext) auto

declare parse_nodes.simps [unfolded oneof_closed,
  unfolded If_removal [of "\<lambda> e. e = ''/>''"], code]

definition parse_node :: "xml parser"
where
  "parse_node = do {
    exactly ''<'';
    n \<leftarrow> parse_name;
    atts \<leftarrow> parse_attributes;
    e \<leftarrow> oneof [''/>'', ''>''];
    if e = ''/>'' then return (XML n atts [])
    else do {
      cs \<leftarrow> parse_nodes;
      exactly ''</'';
      exactly n;
      exactly ''>'';
      return (XML n atts cs)
    }
  }"

declare parse_node_def [unfolded oneof_closed, code]

function parse_header :: "string list parser"
where
  "parse_header ts =
    (if take 2 (trim ts) = ''<?'' then (do {
      h \<leftarrow> scan_upto ''?>'';
      hs \<leftarrow> parse_header;
      return (h # hs)
    }) ts else (do {
      spaces;
      return []
    }) ts)"
  by pat_completeness auto

termination parse_header
proof
  fix ts y tsa
  assume "scan_upto ''?>'' ts = Inr (y, tsa)"
  with is_cparser_scan_upto have "length ts > length tsa"
    unfolding is_cparser_def by force
  then show "(tsa, ts) \<in> measure length" by simp
qed simp

consts scala :: bool

code_printing
  constant scala \<rightharpoonup>
    (Haskell) "False" and
    (Scala) "true" and
    (SML) "false" and
    (OCaml) "false" and
    (Eval) "false"

fun remove_comments_aux :: "bool \<Rightarrow> string \<Rightarrow> string"
where
  "remove_comments_aux False (c # cs) =
    (if c = CHR ''<'' \<and> take 3 cs = ''!--'' then remove_comments_aux True (tl cs)
    else c # remove_comments_aux False cs)" |
  "remove_comments_aux True (c # cs) =
    (if c = CHR ''-'' \<and> take 2 cs = ''->'' then remove_comments_aux False (drop 2 cs)
    else remove_comments_aux True cs)" |
  "remove_comments_aux _ [] = []"

fun remove_comments_aux_acc :: "string \<Rightarrow> bool \<Rightarrow> string \<Rightarrow> string"
where
  "remove_comments_aux_acc a False (c # cs) =
    (if c = CHR ''<'' \<and> take 3 cs = ''!--'' then remove_comments_aux_acc a True (tl cs)
    else remove_comments_aux_acc (c # a) False cs)" |
  "remove_comments_aux_acc a True (c # cs) =
    (if c = CHR ''-'' \<and> take 2 cs = ''->'' then remove_comments_aux_acc a False (drop 2 cs)
    else remove_comments_aux_acc a True cs)" |
  "remove_comments_aux_acc a _ [] = a"

text \<open>A tail recursive variant for Scala to reduce stack size at the cost of double traversal.\<close>
definition remove_comments :: "string \<Rightarrow> string"
where
  "remove_comments =
    (if scala then rev o (remove_comments_aux_acc [] False)
    else remove_comments_aux False)"

hide_const remove_comments_aux remove_comments_aux_acc

definition parse_doc :: "xmldoc parser"
where
  "parse_doc = do {
    update_tokens remove_comments;
    h \<leftarrow> parse_header;
    xml \<leftarrow> parse_node;
    eoi;
    return (XMLDOC h xml)
  }"

definition doc_of_string :: "string \<Rightarrow> string + xmldoc"
where
  "doc_of_string s = do {
    (doc, _) \<leftarrow> parse_doc s;
    Error_Monad.return doc
  }"

end

