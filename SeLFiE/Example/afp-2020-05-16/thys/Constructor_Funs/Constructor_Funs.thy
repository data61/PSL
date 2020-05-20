section \<open>Introduction\<close>

theory Constructor_Funs
  imports Main
  keywords "constructor_funs" :: thy_decl
begin

text \<open>
  Importing this theory adds a preprocessing step to the code generator: All datatype constructors
  are replaced by functions, and all constructor calls are replaced by function calls. For example,
  for the @{const Suc} constructor of @{const nat}, a new constant with the same type and the
  definition @{term \<open>suc' n = Suc n\<close>} is created. Then, all instances of @{const Suc} (except for
  in the constructor functions themselves) are replaced. Note that the constructor functions are
  defined in eta-long form.

  Note that this does not affect constructors declared by @{command code_datatype}, only
  @{command datatype} (and @{command free_constructors}).

  The motivation for doing this is to avoid target-specific lambda-insertion by the code generator.
  In some target languages, constructors cannot be used as functions. As a consequence, terms like
  @{term \<open>map Suc xs\<close>} have to be printed as \<open>map (fn x => Suc x) xs)\<close>. This entails generation of
  fresh names outside of the proof kernel. The transformation provided by this theory ensures that
  all constructor calls are fully saturated. This makes supporting target languages that forbid
  partially-applied constructor calls much easier.

  The obvious downside is that this construction will usually degrade performance of generated code.
  To some extent, an optimising compiler that performs inlining can alleviate that.
\<close>

section \<open>Setup\<close>

ML_file \<open>constructor_funs.ML\<close>
setup \<open>Constructor_Funs.setup\<close>

end
