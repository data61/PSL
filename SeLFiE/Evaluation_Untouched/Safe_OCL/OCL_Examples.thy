(*  Title:       Safe OCL
    Author:      Denis Nikiforov, March 2019
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
chapter \<open>Examples\<close>
theory OCL_Examples
  imports OCL_Normalization
begin

(*** Classes ****************************************************************)

section \<open>Classes\<close>

datatype classes1 =
  Object | Person | Employee | Customer | Project | Task | Sprint

inductive subclass1 where
  "c \<noteq> Object \<Longrightarrow>
   subclass1 c Object"
| "subclass1 Employee Person"
| "subclass1 Customer Person"

instantiation classes1 :: semilattice_sup
begin

definition "(<) \<equiv> subclass1"
definition "(\<le>) \<equiv> subclass1\<^sup>=\<^sup>="

fun sup_classes1 where
  "Object \<squnion> _ = Object"
| "Person \<squnion> c = (if c = Person \<or> c = Employee \<or> c = Customer
    then Person else Object)"
| "Employee \<squnion> c = (if c = Employee then Employee else
    if c = Person \<or> c = Customer then Person else Object)"
| "Customer \<squnion> c = (if c = Customer then Customer else
    if c = Person \<or> c = Employee then Person else Object)"
| "Project \<squnion> c = (if c = Project then Project else Object)"
| "Task \<squnion> c = (if c = Task then Task else Object)"
| "Sprint \<squnion> c = (if c = Sprint then Sprint else Object)"

lemma less_le_not_le_classes1:
  "c < d \<longleftrightarrow> c \<le> d \<and> \<not> d \<le> c"
  for c d :: classes1
  unfolding less_classes1_def less_eq_classes1_def
  using subclass1.simps by auto

lemma order_refl_classes1:
  "c \<le> c"
  for c :: classes1
  unfolding less_eq_classes1_def by simp

lemma order_trans_classes1:
  "c \<le> d \<Longrightarrow> d \<le> e \<Longrightarrow> c \<le> e"
  for c d e :: classes1
  unfolding less_eq_classes1_def
  using subclass1.simps by auto

lemma antisym_classes1:
  "c \<le> d \<Longrightarrow> d \<le> c \<Longrightarrow> c = d"
  for c d :: classes1
  unfolding less_eq_classes1_def
  using subclass1.simps by auto

lemma sup_ge1_classes1:
  "c \<le> c \<squnion> d"
  for c d :: classes1
  by (induct c; auto simp add: less_eq_classes1_def less_classes1_def subclass1.simps)

lemma sup_ge2_classes1:
  "d \<le> c \<squnion> d"
  for c d :: classes1
  by (induct c; auto simp add: less_eq_classes1_def less_classes1_def subclass1.simps)

lemma sup_least_classes1:
  "c \<le> e \<Longrightarrow> d \<le> e \<Longrightarrow> c \<squnion> d \<le> e"
  for c d e :: classes1
  by (induct c; induct d;
      auto simp add: less_eq_classes1_def less_classes1_def subclass1.simps)

instance
  apply intro_classes
  apply (simp add: less_le_not_le_classes1)
  apply (simp add: order_refl_classes1)
  apply (rule order_trans_classes1; auto)
  apply (simp add: antisym_classes1)
  apply (simp add: sup_ge1_classes1)
  apply (simp add: sup_ge2_classes1)
  by (simp add: sup_least_classes1)

end

code_pred subclass1 .

fun subclass1_fun where
  "subclass1_fun Object \<C> = False"
| "subclass1_fun Person \<C> = (\<C> = Object)"
| "subclass1_fun Employee \<C> = (\<C> = Object \<or> \<C> = Person)"
| "subclass1_fun Customer \<C> = (\<C> = Object \<or> \<C> = Person)"
| "subclass1_fun Project \<C> = (\<C> = Object)"
| "subclass1_fun Task \<C> = (\<C> = Object)"
| "subclass1_fun Sprint \<C> = (\<C> = Object)"

lemma less_classes1_code [code]:
  "(<) = subclass1_fun"
proof (intro ext iffI)
  fix \<C> \<D> :: "classes1"
  show "\<C> < \<D> \<Longrightarrow> subclass1_fun \<C> \<D>"
    unfolding less_classes1_def
    apply (erule subclass1.cases, auto)
    using subclass1_fun.elims(3) by blast
  show "subclass1_fun \<C> \<D> \<Longrightarrow> \<C> < \<D>"
    by (erule subclass1_fun.elims, auto simp add: less_classes1_def subclass1.intros)
qed

lemma less_eq_classes1_code [code]:
  "(\<le>) = (\<lambda>x y. subclass1_fun x y \<or> x = y)"
  unfolding dual_order.order_iff_strict less_classes1_code
  by auto

(*** Object Model ***********************************************************)

section \<open>Object Model\<close>

abbreviation "\<Gamma>\<^sub>0 \<equiv> fmempty :: classes1 type env"
declare [[coercion "ObjectType :: classes1 \<Rightarrow> classes1 basic_type"]]
declare [[coercion "phantom :: String.literal \<Rightarrow> classes1 enum"]]

instantiation classes1 :: ocl_object_model
begin

definition "classes_classes1 \<equiv>
  {|Object, Person, Employee, Customer, Project, Task, Sprint|}"

definition "attributes_classes1 \<equiv> fmap_of_list [
  (Person, fmap_of_list [
    (STR ''name'', String[1] :: classes1 type)]),
  (Employee, fmap_of_list [
    (STR ''name'', String[1]),
    (STR ''position'', String[1])]),
  (Customer, fmap_of_list [
    (STR ''vip'', Boolean[1])]),
  (Project, fmap_of_list [
    (STR ''name'', String[1]),
    (STR ''cost'', Real[?])]),
  (Task, fmap_of_list [
    (STR ''description'', String[1])])]"

abbreviation "assocs \<equiv> [
  STR ''ProjectManager'' \<mapsto>\<^sub>f [
    STR ''projects'' \<mapsto>\<^sub>f (Project, 0::nat, \<infinity>::enat, False, True),
    STR ''manager'' \<mapsto>\<^sub>f (Employee, 1, 1, False, False)],
  STR ''ProjectMember'' \<mapsto>\<^sub>f [
    STR ''member_of'' \<mapsto>\<^sub>f (Project, 0, \<infinity>, False, False),
    STR ''members'' \<mapsto>\<^sub>f (Employee, 1, 20, True, True)],
  STR ''ManagerEmployee'' \<mapsto>\<^sub>f [
    STR ''line_manager'' \<mapsto>\<^sub>f (Employee, 0, 1, False, False),
    STR ''project_manager'' \<mapsto>\<^sub>f (Employee, 0, \<infinity>, False, False),
    STR ''employees'' \<mapsto>\<^sub>f (Employee, 3, 7, False, False)],
  STR ''ProjectCustomer'' \<mapsto>\<^sub>f [
    STR ''projects'' \<mapsto>\<^sub>f (Project, 0, \<infinity>, False, True),
    STR ''customer'' \<mapsto>\<^sub>f (Customer, 1, 1, False, False)],
  STR ''ProjectTask'' \<mapsto>\<^sub>f [
    STR ''project'' \<mapsto>\<^sub>f (Project, 1, 1, False, False),
    STR ''tasks'' \<mapsto>\<^sub>f (Task, 0, \<infinity>, True, True)],
  STR ''SprintTaskAssignee'' \<mapsto>\<^sub>f [
    STR ''sprint'' \<mapsto>\<^sub>f (Sprint, 0, 10, False, True),
    STR ''tasks'' \<mapsto>\<^sub>f (Task, 0, 5, False, True),
    STR ''assignee'' \<mapsto>\<^sub>f (Employee, 0, 1, False, False)]]"

definition "associations_classes1 \<equiv> assocs"

definition "association_classes_classes1 \<equiv> fmempty :: classes1 \<rightharpoonup>\<^sub>f assoc"

text \<open>
\begin{verbatim}
context Project
def: membersCount() : Integer[1] = members->size()
def: membersByName(mn : String[1]) : Set(Employee[1]) =
       members->select(member | member.name = mn)
static def: allProjects() : Set(Project[1]) =
              Project[1].allInstances()
\end{verbatim}\<close>

definition "operations_classes1 \<equiv> [
  (STR ''membersCount'', Project[1], [], Integer[1], False,
   Some (OperationCall
    (AssociationEndCall (Var STR ''self'') DotCall None STR ''members'')
    ArrowCall CollectionSizeOp [])),
  (STR ''membersByName'', Project[1], [(STR ''mn'', String[1], In)],
    Set Employee[1], False,
   Some (SelectIteratorCall
    (AssociationEndCall (Var STR ''self'') DotCall None STR ''members'')
    ArrowCall [STR ''member''] None
    (OperationCall
      (AttributeCall (Var STR ''member'') DotCall STR ''name'')
      DotCall EqualOp [Var STR ''mn'']))),
  (STR ''allProjects'', Project[1], [], Set Project[1], True,
   Some (MetaOperationCall Project[1] AllInstancesOp))
  ] :: (classes1 type, classes1 expr) oper_spec list"

definition "literals_classes1 \<equiv> fmap_of_list [
  (STR ''E1'' :: classes1 enum, {|STR ''A'', STR ''B''|}),
  (STR ''E2'', {|STR ''C'', STR ''D'', STR ''E''|})]"


lemma assoc_end_min_less_eq_max:
  "assoc |\<in>| fmdom assocs \<Longrightarrow>
   fmlookup assocs assoc = Some ends \<Longrightarrow>
   role |\<in>| fmdom ends  \<Longrightarrow>
   fmlookup ends role = Some end \<Longrightarrow>
   assoc_end_min end \<le> assoc_end_max end"
  unfolding assoc_end_min_def assoc_end_max_def
  using zero_enat_def one_enat_def numeral_eq_enat by auto

lemma association_ends_unique:
  assumes "association_ends' classes assocs \<C> from role end\<^sub>1"
      and "association_ends' classes assocs \<C> from role end\<^sub>2"
    shows "end\<^sub>1 = end\<^sub>2"
proof -
  have "\<not> association_ends_not_unique' classes assocs" by eval
  with assms show ?thesis
    using association_ends_not_unique'.simps by blast
qed

instance
  apply standard
  unfolding associations_classes1_def
  using assoc_end_min_less_eq_max apply blast
  using association_ends_unique by blast

end

(*** Simplification Rules ***************************************************)

section \<open>Simplification Rules\<close>

lemma ex_alt_simps [simp]:
  "\<exists>a. a"
  "\<exists>a. \<not> a"
  "(\<exists>a. (a \<longrightarrow> P) \<and> a) = P"
  "(\<exists>a. \<not> a \<and> (\<not> a \<longrightarrow> P)) = P"
  by auto

declare numeral_eq_enat [simp]

lemmas basic_type_le_less [simp] = Orderings.order_class.le_less
  for x y :: "'a basic_type"

declare element_type_alt_simps [simp]
declare update_element_type.simps [simp]
declare to_unique_collection.simps [simp]
declare to_nonunique_collection.simps [simp]
declare to_ordered_collection.simps [simp]

declare assoc_end_class_def [simp]
declare assoc_end_min_def [simp]
declare assoc_end_max_def [simp]
declare assoc_end_ordered_def [simp]
declare assoc_end_unique_def [simp]

declare oper_name_def [simp]
declare oper_context_def [simp]
declare oper_params_def [simp]
declare oper_result_def [simp]
declare oper_static_def [simp]
declare oper_body_def [simp]

declare oper_in_params_def [simp]
declare oper_out_params_def [simp]

declare assoc_end_type_def [simp]
declare oper_type_def [simp]

declare op_type_alt_simps [simp]
declare typing_alt_simps [simp]
declare normalize_alt_simps [simp]
declare nf_typing.simps [simp]

declare subclass1.intros [intro]
declare less_classes1_def [simp]

declare literals_classes1_def [simp]

lemma attribute_Employee_name [simp]:
  "attribute Employee STR ''name'' \<D> \<tau> =
   (\<D> = Employee \<and> \<tau> = String[1])"
proof -
  have "attribute Employee STR ''name'' Employee String[1]"
    by eval
  thus ?thesis
    using attribute_det by blast
qed

lemma association_end_Project_members [simp]:
  "association_end Project None STR ''members'' \<D> \<tau> =
   (\<D> = Project \<and> \<tau> = (Employee, 1, 20, True, True))"
proof -
  have "association_end Project None STR ''members''
          Project (Employee, 1, 20, True, True)"
    by eval
  thus ?thesis
    using association_end_det by blast
qed

lemma association_end_Employee_projects_simp [simp]:
  "association_end Employee None STR ''projects'' \<D> \<tau> =
   (\<D> = Employee \<and> \<tau> = (Project, 0, \<infinity>, False, True))"
proof -
  have "association_end Employee None STR ''projects''
          Employee (Project, 0, \<infinity>, False, True)"
    by eval
  thus ?thesis
    using association_end_det by blast
qed

lemma static_operation_Project_allProjects [simp]:
  "static_operation \<langle>Project\<rangle>\<^sub>\<T>[1] STR ''allProjects'' [] oper =
   (oper = (STR ''allProjects'', \<langle>Project\<rangle>\<^sub>\<T>[1], [], Set \<langle>Project\<rangle>\<^sub>\<T>[1], True,
     Some (MetaOperationCall \<langle>Project\<rangle>\<^sub>\<T>[1] AllInstancesOp)))"
proof -
  have "static_operation \<langle>Project\<rangle>\<^sub>\<T>[1] STR ''allProjects'' []
    (STR ''allProjects'', \<langle>Project\<rangle>\<^sub>\<T>[1], [], Set \<langle>Project\<rangle>\<^sub>\<T>[1], True,
     Some (MetaOperationCall \<langle>Project\<rangle>\<^sub>\<T>[1] AllInstancesOp))"
    by eval
  thus ?thesis
    using static_operation_det by blast
qed

(*** Basic Types ************************************************************)

section \<open>Basic Types\<close>

subsection \<open>Positive Cases\<close>

lemma "UnlimitedNatural < (Real :: classes1 basic_type)" by simp
lemma "\<langle>Employee\<rangle>\<^sub>\<T> < \<langle>Person\<rangle>\<^sub>\<T>" by auto
lemma "\<langle>Person\<rangle>\<^sub>\<T> \<le> OclAny" by simp

subsection \<open>Negative Cases\<close>

lemma "\<not> String \<le> (Boolean :: classes1 basic_type)" by simp

(*** Types ******************************************************************)

section \<open>Types\<close>

subsection \<open>Positive Cases\<close>

lemma "Integer[?] < (OclSuper :: classes1 type)" by simp
lemma "Collection Real[?] < (OclSuper :: classes1 type)" by simp
lemma "Set (Collection Boolean[1]) < (OclSuper :: classes1 type)" by simp
lemma "Set (Bag Boolean[1]) < Set (Collection Boolean[?] :: classes1 type)"
  by simp
lemma "Tuple (fmap_of_list [(STR ''a'', Boolean[1]), (STR ''b'', Integer[1])]) <
       Tuple (fmap_of_list [(STR ''a'', Boolean[?] :: classes1 type)])" by eval

lemma "Integer[1] \<squnion> (Real[?] :: classes1 type) = Real[?]" by simp
lemma "Set Integer[1] \<squnion> Set (Real[1] :: classes1 type) = Set Real[1]" by simp
lemma "Set Integer[1] \<squnion> Bag (Boolean[?] :: classes1 type) = Collection OclAny[?]"
  by simp
lemma "Set Integer[1] \<squnion> (Real[1] :: classes1 type) = OclSuper" by simp

subsection \<open>Negative Cases\<close>

lemma "\<not> OrderedSet Boolean[1] < Set (Boolean[1] :: classes1 type)" by simp

(*** Typing *****************************************************************)

section \<open>Typing\<close>

subsection \<open>Positive Cases\<close>

text \<open>
\<^verbatim>\<open>E1::A : E1[1]\<close>\<close>
lemma
  "\<Gamma>\<^sub>0 \<turnstile> EnumLiteral STR ''E1'' STR ''A'' : (Enum STR ''E1'')[1]"
  by simp

text \<open>
\<^verbatim>\<open>true or false : Boolean[1]\<close>\<close>
lemma
  "\<Gamma>\<^sub>0 \<turnstile> OperationCall (BooleanLiteral True) DotCall OrOp
    [BooleanLiteral False] : Boolean[1]"
  by simp

text \<open>
\<^verbatim>\<open>null and true : Boolean[?]\<close>\<close>
lemma
  "\<Gamma>\<^sub>0 \<turnstile> OperationCall (NullLiteral) DotCall AndOp
    [BooleanLiteral True] : Boolean[?]"
  by simp

text \<open>
\<^verbatim>\<open>let x : Real[1] = 5 in x + 7 : Real[1]\<close>\<close>
lemma
  "\<Gamma>\<^sub>0 \<turnstile> Let (STR ''x'') (Some Real[1]) (IntegerLiteral 5)
    (OperationCall (Var STR ''x'') DotCall PlusOp [IntegerLiteral 7]) : Real[1]"
  by simp

text \<open>
\<^verbatim>\<open>null.oclIsUndefined() : Boolean[1]\<close>\<close>
lemma
  "\<Gamma>\<^sub>0 \<turnstile> OperationCall (NullLiteral) DotCall OclIsUndefinedOp [] : Boolean[1]"
  by simp

text \<open>
\<^verbatim>\<open>Sequence{1..5, null}.oclIsUndefined() : Sequence(Boolean[1])\<close>\<close>
lemma
  "\<Gamma>\<^sub>0 \<turnstile> OperationCall (CollectionLiteral SequenceKind
    [CollectionRange (IntegerLiteral 1) (IntegerLiteral 5),
     CollectionItem NullLiteral])
    DotCall OclIsUndefinedOp [] : Sequence Boolean[1]"
  by simp

text \<open>
\<^verbatim>\<open>Sequence{1..5}->product(Set{'a', 'b'})
  : Set(Tuple(first: Integer[1], second: String[1]))\<close>\<close>
lemma
  "\<Gamma>\<^sub>0 \<turnstile> OperationCall (CollectionLiteral SequenceKind
    [CollectionRange (IntegerLiteral 1) (IntegerLiteral 5)])
    ArrowCall ProductOp
    [CollectionLiteral SetKind
      [CollectionItem (StringLiteral ''a''),
       CollectionItem (StringLiteral ''b'')]] :
    Set (Tuple (fmap_of_list [
      (STR ''first'', Integer[1]), (STR ''second'', String[1])]))"
  by simp

text \<open>
\<^verbatim>\<open>Sequence{1..5, null}?->iterate(x, acc : Real[1] = 0 | acc + x)
  : Real[1]\<close>\<close>
lemma
  "\<Gamma>\<^sub>0 \<turnstile> IterateCall (CollectionLiteral SequenceKind
    [CollectionRange (IntegerLiteral 1) (IntegerLiteral 5),
     CollectionItem NullLiteral]) SafeArrowCall
    [STR ''x''] None
    (STR ''acc'') (Some Real[1]) (IntegerLiteral 0)
    (OperationCall (Var STR ''acc'') DotCall PlusOp [Var STR ''x'']) : Real[1]"
  by simp

text \<open>
\<^verbatim>\<open>Sequence{1..5, null}?->max() : Integer[1]\<close>\<close>
lemma
  "\<Gamma>\<^sub>0 \<turnstile> OperationCall (CollectionLiteral SequenceKind
    [CollectionRange (IntegerLiteral 1) (IntegerLiteral 5),
     CollectionItem NullLiteral])
    SafeArrowCall CollectionMaxOp [] : Integer[1]"
  by simp

text \<open>
\<^verbatim>\<open>let x : Sequence(String[?]) = Sequence{'abc', 'zxc'} in
x->any(it | it = 'test') : String[?]\<close>\<close>
lemma
  "\<Gamma>\<^sub>0 \<turnstile> Let (STR ''x'') (Some (Sequence String[?]))
    (CollectionLiteral SequenceKind
      [CollectionItem (StringLiteral ''abc''),
       CollectionItem (StringLiteral ''zxc'')])
    (AnyIteratorCall (Var STR ''x'') ArrowCall
      [STR ''it''] None
      (OperationCall (Var STR ''it'') DotCall EqualOp
        [StringLiteral ''test''])) : String[?]"
  by simp

text \<open>
\<^verbatim>\<open>let x : Sequence(String[?]) = Sequence{'abc', 'zxc'} in
x?->closure(it | it) : OrderedSet(String[1])\<close>\<close>
lemma
  "\<Gamma>\<^sub>0 \<turnstile> Let STR ''x'' (Some (Sequence String[?]))
    (CollectionLiteral SequenceKind
      [CollectionItem (StringLiteral ''abc''),
       CollectionItem (StringLiteral ''zxc'')])
    (ClosureIteratorCall (Var STR ''x'') SafeArrowCall
      [STR ''it''] None
      (Var STR ''it'')) : OrderedSet String[1]"
  by simp

text \<open>
\<^verbatim>\<open>context Employee:
name : String[1]\<close>\<close>
lemma
  "\<Gamma>\<^sub>0(STR ''self'' \<mapsto>\<^sub>f Employee[1]) \<turnstile>
    AttributeCall (Var STR ''self'') DotCall STR ''name'' : String[1]"
  by simp

text \<open>
\<^verbatim>\<open>context Employee:
projects : Set(Project[1])\<close>\<close>
lemma
  "\<Gamma>\<^sub>0(STR ''self'' \<mapsto>\<^sub>f Employee[1]) \<turnstile>
    AssociationEndCall (Var STR ''self'') DotCall None
      STR ''projects'' : Set Project[1]"
  by simp

text \<open>
\<^verbatim>\<open>context Employee:
projects.members : Bag(Employee[1])\<close>\<close>
lemma
  "\<Gamma>\<^sub>0(STR ''self'' \<mapsto>\<^sub>f Employee[1]) \<turnstile>
    AssociationEndCall (AssociationEndCall (Var STR ''self'')
        DotCall None STR ''projects'')
      DotCall None STR ''members'' : Bag Employee[1]"
  by simp

text \<open>
\<^verbatim>\<open>Project[?].allInstances() : Set(Project[?])\<close>\<close>
lemma
  "\<Gamma>\<^sub>0 \<turnstile> MetaOperationCall Project[?] AllInstancesOp : Set Project[?]"
  by simp

text \<open>
\<^verbatim>\<open>Project[1]::allProjects() : Set(Project[1])\<close>\<close>
lemma
  "\<Gamma>\<^sub>0 \<turnstile> StaticOperationCall Project[1] STR ''allProjects'' [] : Set Project[1]"
  by simp

subsection \<open>Negative Cases\<close>

text \<open>
\<^verbatim>\<open>true = null\<close>\<close>
lemma
  "\<nexists>\<tau>. \<Gamma>\<^sub>0 \<turnstile> OperationCall (BooleanLiteral True) DotCall EqualOp
    [NullLiteral] : \<tau>"
  by simp

text \<open>
\<^verbatim>\<open>let x : Boolean[1] = 5 in x and true\<close>\<close>
lemma
  "\<nexists>\<tau>. \<Gamma>\<^sub>0 \<turnstile> Let STR ''x'' (Some Boolean[1]) (IntegerLiteral 5)
    (OperationCall (Var STR ''x'') DotCall AndOp [BooleanLiteral True]) : \<tau>"
  by simp

text \<open>
\<^verbatim>\<open>let x : Sequence(String[?]) = Sequence{'abc', 'zxc'} in
x->closure(it | 1)\<close>\<close>
lemma
  "\<nexists>\<tau>. \<Gamma>\<^sub>0 \<turnstile> Let STR ''x'' (Some (Sequence String[?]))
    (CollectionLiteral SequenceKind
      [CollectionItem (StringLiteral ''abc''),
       CollectionItem (StringLiteral ''zxc'')])
    (ClosureIteratorCall (Var STR ''x'') ArrowCall [STR ''it''] None
      (IntegerLiteral 1)) : \<tau>"
  by simp

text \<open>
\<^verbatim>\<open>Sequence{1..5, null}->max()\<close>\<close>
lemma
  "\<nexists>\<tau>. \<Gamma>\<^sub>0 \<turnstile> OperationCall (CollectionLiteral SequenceKind
    [CollectionRange (IntegerLiteral 1) (IntegerLiteral 5),
     CollectionItem NullLiteral])
    ArrowCall CollectionMaxOp [] : \<tau>"
proof -
  have "\<not> operation_defined (Integer[?] :: classes1 type) STR ''max'' [Integer[?]]"
    by eval
  thus ?thesis by simp
qed

(*** Code *******************************************************************)

section \<open>Code\<close>

subsection \<open>Positive Cases\<close>

values "{(\<D>, \<tau>). attribute Employee STR ''name'' \<D> \<tau>}"
values "{(\<D>, end). association_end Employee None STR ''employees'' \<D> end}"
values "{(\<D>, end). association_end Employee (Some STR ''project_manager'') STR ''employees'' \<D> end}"
values "{op. operation Project[1] STR ''membersCount'' [] op}"
values "{op. operation Project[1] STR ''membersByName'' [String[1]] op}"
value "has_literal STR ''E1'' STR ''A''"

text \<open>
\<^verbatim>\<open>context Employee:
projects.members : Bag(Employee[1])\<close>\<close>
values
  "{\<tau>. \<Gamma>\<^sub>0(STR ''self'' \<mapsto>\<^sub>f Employee[1]) \<turnstile>
    AssociationEndCall (AssociationEndCall (Var STR ''self'')
        DotCall None STR ''projects'')
      DotCall None STR ''members'' : \<tau>}"

subsection \<open>Negative Cases\<close>

values "{(\<D>, \<tau>). attribute Employee STR ''name2'' \<D> \<tau>}"
value "has_literal STR ''E1'' STR ''C''"

text \<open>
\<^verbatim>\<open>Sequence{1..5, null}->max()\<close>\<close>
values
  "{\<tau>. \<Gamma>\<^sub>0 \<turnstile> OperationCall (CollectionLiteral SequenceKind
    [CollectionRange (IntegerLiteral 1) (IntegerLiteral 5),
      CollectionItem NullLiteral])
    ArrowCall CollectionMaxOp [] : \<tau>}"

end
