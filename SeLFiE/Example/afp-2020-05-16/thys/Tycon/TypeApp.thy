section \<open>Type Application\<close>

theory TypeApp
imports HOLCF
begin

subsection \<open>Class of type constructors\<close>

text \<open>In HOLCF, the type @{typ "udom defl"} consists of deflations
over the universal domain---each value of type @{typ "udom defl"}
represents a bifinite domain. In turn, values of the continuous
function type @{typ "udom defl \<rightarrow> udom defl"} represent functions from
domains to domains, i.e.~type constructors.\<close>

text \<open>Class \<open>tycon\<close>, defined below, will be populated with
dummy types: For example, if the type \<open>foo\<close> is an instance of
class \<open>tycon\<close>, then users will never deal with any values \<open>x::foo\<close> in practice. Such types are only used with the overloaded
constant \<open>tc\<close>, which associates each type \<open>'a::tycon\<close>
with a value of type @{typ "udom defl \<rightarrow> udom defl"}. \medskip\<close>

class tycon =
  fixes tc :: "('a::type) itself \<Rightarrow> udom defl \<rightarrow> udom defl"

text \<open>Type @{typ "'a itself"} is defined in Isabelle's meta-logic;
it is inhabited by a single value, written @{term "TYPE('a)"}. We
define the syntax \<open>TC('a)\<close> to abbreviate \<open>tc
TYPE('a)\<close>. \medskip\<close>

syntax  "_TC" :: "type \<Rightarrow> logic"  ("(1TC/(1'(_')))")

translations "TC('a)" \<rightleftharpoons> "CONST tc TYPE('a)"


subsection \<open>Type constructor for type application\<close>

text \<open>We now define a binary type constructor that models type
application: Type \<open>('a, 't) app\<close> is the result of applying the
type constructor \<open>'t\<close> (from class \<open>tycon\<close>) to the type
argument \<open>'a\<close> (from class \<open>domain\<close>).\<close>

text \<open>We define type \<open>('a, 't) app\<close> using \<open>domaindef\<close>,
a low-level type-definition command provided by HOLCF (similar to
\<open>typedef\<close> in Isabelle/HOL) that defines a new domain type
represented by the given deflation. Note that in HOLCF, \<open>DEFL('a)\<close> is an abbreviation for \<open>defl TYPE('a)\<close>, where
\<open>defl :: ('a::domain) itself \<Rightarrow> udom defl\<close> is an overloaded
function from the \<open>domain\<close> type class that yields the deflation
representing the given type. \medskip\<close>

domaindef ('a,'t) app = "TC('t::tycon)\<cdot>DEFL('a::domain)"

text \<open>We define the infix syntax \<open>'a\<cdot>'t\<close> for the type \<open>('a,'t) app\<close>. Note that for consistency with Isabelle's existing
type syntax, we have used postfix order for type application: type
argument on the left, type constructor on the right. \medskip\<close>

type_notation app ("(_\<cdot>_)" [999,1000] 999)

text \<open>The \<open>domaindef\<close> command generates the theorem \<open>DEFL_app\<close>: @{thm DEFL_app [where 'a="'a::domain" and 't="'t::tycon"]},
which we can use to derive other useful lemmas. \medskip\<close>

lemma TC_DEFL: "TC('t::tycon)\<cdot>DEFL('a) = DEFL('a\<cdot>'t)"
by (rule DEFL_app [symmetric])

lemma DEFL_app_mono [simp, intro]:
  "DEFL('a) \<sqsubseteq> DEFL('b) \<Longrightarrow> DEFL('a\<cdot>'t::tycon) \<sqsubseteq> DEFL('b\<cdot>'t)"
 apply (simp add: DEFL_app)
 apply (erule monofun_cfun_arg)
done

end
