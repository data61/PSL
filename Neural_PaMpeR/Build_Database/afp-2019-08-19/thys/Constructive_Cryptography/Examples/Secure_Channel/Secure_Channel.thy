section \<open>Secure composition: Encrypt then MAC\<close>

theory Secure_Channel imports
  One_Time_Pad
  Message_Authentication_Code
begin

context begin
interpretation INSEC: insec_channel .

interpretation MAC: macode "rnd \<eta>" "mac \<eta>" for \<eta> . 
interpretation AUTH: auth_channel . 

interpretation CIPHER: cipher "key \<eta>" "enc \<eta>" "dec \<eta>" for \<eta> . 
interpretation SEC: sec_channel .

lemma plossless_enc [plossless_intro]:
  "plossless_converter (\<I>_uniform (nlists UNIV \<eta>) UNIV) (\<I>_uniform UNIV (nlists UNIV \<eta>) \<oplus>\<^sub>\<I> \<I>_uniform (nlists UNIV \<eta>) UNIV) (CIPHER.enc \<eta>)"
  unfolding CIPHER.enc_def
  by(rule plossless_converter_of_callee) (auto simp add: stateless_callee_def enc_def in_nlists_UNIV)

lemma plossless_dec [plossless_intro]:
  "plossless_converter (\<I>_uniform UNIV (insert None (Some ` nlists UNIV \<eta>))) (\<I>_uniform UNIV (nlists UNIV \<eta>) \<oplus>\<^sub>\<I> \<I>_uniform UNIV (insert None (Some ` nlists UNIV \<eta>))) (CIPHER.dec \<eta>)"
  unfolding CIPHER.dec_def
  by(rule plossless_converter_of_callee) (auto simp add: stateless_callee_def dec_def in_nlists_UNIV split: option.split)

lemma callee_invariant_on_key_oracle:
  "callee_invariant_on
     (CIPHER.KEY.key_oracle \<eta> \<oplus>\<^sub>O CIPHER.KEY.key_oracle \<eta>)
     (\<lambda>x. case x of None \<Rightarrow> True | Some x' \<Rightarrow> length x' = \<eta>)
     (\<I>_uniform UNIV (nlists UNIV \<eta>) \<oplus>\<^sub>\<I> \<I>_full)"
proof(unfold_locales, goal_cases)
  case (1 s x y s')
  then show ?case by(cases x; clarsimp split: option.splits; simp add: key_def in_nlists_UNIV)
next
  case (2 s)
  then show ?case by(clarsimp intro!: WT_calleeI split: option.split_asm)(simp_all add: in_nlists_UNIV key_def)
qed

interpretation key: callee_invariant_on
  "CIPHER.KEY.key_oracle \<eta> \<oplus>\<^sub>O CIPHER.KEY.key_oracle \<eta>"
  "\<lambda>x. case x of None \<Rightarrow> True | Some x' \<Rightarrow> length x' = \<eta>"
  "\<I>_uniform UNIV (nlists UNIV \<eta>) \<oplus>\<^sub>\<I> \<I>_full" for \<eta>
  by(rule callee_invariant_on_key_oracle)

lemma WT_enc [WT_intro]: "\<I>_uniform (nlists UNIV \<eta>) UNIV,
  \<I>_uniform UNIV (nlists UNIV \<eta>) \<oplus>\<^sub>\<I> \<I>_uniform (vld \<eta>) UNIV \<turnstile>\<^sub>C CIPHER.enc \<eta> \<surd>"
  unfolding CIPHER.enc_def
  by (rule WT_converter_of_callee) (simp_all add: stateless_callee_def vld_def enc_def in_nlists_UNIV)

lemma WT_dec [WT_intro]: "\<I>_uniform UNIV (insert None (Some ` nlists UNIV \<eta>)),
    \<I>_uniform UNIV (nlists UNIV \<eta>) \<oplus>\<^sub>\<I> \<I>_uniform UNIV (insert None (Some ` vld \<eta>)) \<turnstile>\<^sub>C
    CIPHER.dec \<eta> \<surd>"
  unfolding CIPHER.dec_def
  by(rule WT_converter_of_callee)(auto simp add: stateless_callee_def dec_def vld_def in_nlists_UNIV)

lemma bound_enc [interaction_bound]: "interaction_any_bounded_converter (CIPHER.enc \<eta>) (enat 2)"
  unfolding CIPHER.enc_def
  by (rule interaction_any_bounded_converter_of_callee) 
    (auto simp add: stateless_callee_def map_gpv_id_bind_gpv zero_enat_def one_enat_def)

lemma bound_dec [interaction_bound]: "interaction_any_bounded_converter (CIPHER.dec \<eta>) (enat 2)"
  unfolding CIPHER.dec_def
  by (rule interaction_any_bounded_converter_of_callee)
    (auto simp add: stateless_callee_def map_gpv_id_bind_gpv zero_enat_def one_enat_def split: sum.split option.split)

theorem mac_otp:
  defines "\<I>_real \<equiv> \<lambda>\<eta>. \<I>_uniform {x. valid_mac_query \<eta> x} UNIV"
    and "\<I>_ideal \<equiv> \<lambda>_. \<I>_full"
    and "\<I>_common \<equiv> \<lambda>\<eta>. \<I>_uniform (vld \<eta>) UNIV \<oplus>\<^sub>\<I> \<I>_full"
  shows
    "constructive_security
      (\<lambda>\<eta>. 1\<^sub>C |\<^sub>= (CIPHER.enc \<eta> |\<^sub>= CIPHER.dec \<eta>) \<odot> parallel_wiring \<rhd>
            parallel_resource1_wiring \<rhd>
            CIPHER.KEY.res \<eta> \<parallel>
            (1\<^sub>C |\<^sub>= MAC.enm \<eta> |\<^sub>= MAC.dem \<eta> \<rhd>
             1\<^sub>C |\<^sub>= parallel_wiring \<rhd>
             parallel_resource1_wiring \<rhd> MAC.RO.res \<eta> \<parallel> INSEC.res))
      (\<lambda>_. SEC.res)
      (\<lambda>\<eta>. CNV Message_Authentication_Code.sim (Inl None) \<odot> CNV One_Time_Pad.sim None)
      (\<lambda>\<eta>. \<I>_uniform (Set.Collect (valid_mac_query \<eta>)) (insert None (Some ` (nlists UNIV \<eta> \<times> nlists UNIV \<eta>))))
      (\<lambda>\<eta>. \<I>_uniform UNIV {None, Some \<eta>})
      (\<lambda>\<eta>. \<I>_uniform (nlists UNIV \<eta>) UNIV \<oplus>\<^sub>\<I> \<I>_uniform UNIV (insert None (Some ` nlists UNIV \<eta>)))
      (\<lambda>_. enat q) True (\<lambda>\<eta>. (id, map_option length) \<circ>\<^sub>w (insec_query_of, map_option snd))"
proof(rule composability[OF one_time_pad[THEN constructive_security2.constructive_security, unfolded CIPHER.res_alt_def comp_converter_parallel2 comp_converter_id_left]
  secure_mac[unfolded MAC.res_def, 
        THEN constructive_security.parallel_resource1,
        THEN constructive_security.lifting],
      where ?\<I>_res2="\<lambda>\<eta>. \<I>_uniform UNIV (nlists UNIV \<eta>) \<oplus>\<^sub>\<I> \<I>_uniform UNIV (nlists UNIV \<eta>)" and ?bound_conv1="\<lambda>_. 2" and ?q3 = "2 * q" and bound_sim = "\<lambda>_. \<infinity>",
simplified]
    , goal_cases)
  case (1 \<eta>)
  have [simp]: "\<I>_uniform UNIV (nlists UNIV \<eta>) \<turnstile>c CIPHER.KEY.key_oracle \<eta> s \<surd>"
    if "pred_option (\<lambda>x. length x = \<eta>) s" for s \<eta>
    apply(rule WT_calleeI)
    subgoal for call using that by(cases s; cases call; clarsimp; auto simp add: key_def in_nlists_UNIV)
    done
  have *: "callee_invariant_on (CIPHER.KEY.key_oracle \<eta> \<oplus>\<^sub>O CIPHER.KEY.key_oracle \<eta>) (pred_option (\<lambda>x. length x = \<eta>))
     (\<I>_uniform UNIV (nlists UNIV \<eta>) \<oplus>\<^sub>\<I> \<I>_uniform UNIV (nlists UNIV \<eta>))" for \<eta>
    apply(unfold_locales)
    subgoal for s x y s' by(cases s; cases x; clarsimp; auto simp add: key_def in_nlists_UNIV)
    subgoal for s by auto
    done
  then show ?case unfolding CIPHER.KEY.res_def
    by(rule callee_invariant_on.WT_resource_of_oracle) simp

  case (2 \<eta>)
  show ?case 
    unfolding CIPHER.KEY.res_def
    apply(rule callee_invariant_on.lossless_resource_of_oracle[OF *])
    subgoal for s x by(cases s; cases x)(auto split: plus_oracle_split; simp add: key_def)+
    subgoal by simp
    done

  case (3 \<eta>)
  show ?case by(rule WT_intro)+

  case (4 \<eta>)
  show ?case by interaction_bound_converter code_simp

  case (5 \<eta>)
  show ?case by (simp add: max_def) (simp add: times_enat_def)

  case (6 \<eta>)
  show ?case unfolding vld_def by(rule plossless_intro WT_intro[unfolded vld_def])+
qed

end

end
