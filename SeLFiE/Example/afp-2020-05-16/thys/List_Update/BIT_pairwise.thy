
section "BIT is pairwise"

theory BIT_pairwise
imports List_Factoring BIT
begin

lemma L_nths: "S \<subseteq> {..<length init}
  \<Longrightarrow> map_pmf (\<lambda>l. nths l S) (Prob_Theory.bv (length init))
      = (Prob_Theory.bv (length (nths init S)))"
proof(induct init arbitrary: S)
  case (Cons a as)
  then have passt: "{j. Suc j \<in> S} \<subseteq> {..<length as}" by auto

  have " map_pmf (\<lambda>l. nths l S) (Prob_Theory.bv (length (a # as))) = 
    Prob_Theory.bv (length as) \<bind>
    (\<lambda>x. bernoulli_pmf (1 / 2) \<bind>
          (\<lambda>xa. return_pmf
                  ((if 0 \<in> S then [xa] else []) @ nths x {j. Suc j \<in> S})))"
      by(simp add: map_pmf_def bind_return_pmf bind_assoc_pmf nths_Cons) 
  also have "\<dots> = (bernoulli_pmf (1 / 2)) \<bind> 
          (\<lambda>xa. (Prob_Theory.bv (length as) \<bind>
    (\<lambda>x. return_pmf ((if 0 \<in> S then [xa] else []) @ nths x {j. Suc j \<in> S}))))"
        by(rule bind_commute_pmf)
   also have "\<dots> = (bernoulli_pmf (1 / 2)) \<bind> 
          (\<lambda>xa. (map_pmf (\<lambda>x. (nths x {j. Suc j \<in> S})) (Prob_Theory.bv (length as)))
              \<bind>  (\<lambda>xs. return_pmf ((if 0 \<in> S then [xa] else []) @ xs)))"
      by(simp add: bind_return_pmf bind_assoc_pmf map_pmf_def)
   also have "\<dots> = (bernoulli_pmf (1 / 2)) \<bind> 
          (\<lambda>xa. Prob_Theory.bv (length (nths as {j. Suc j \<in> S}))
              \<bind>  (\<lambda>xs. return_pmf ((if 0 \<in> S then [xa] else []) @ xs)))"
        using Cons(1)[OF passt] by auto
   also have "\<dots> = Prob_Theory.bv (length (nths (a # as) S))"
      apply(auto simp add: nths_Cons bind_return_pmf')
      by(rule bind_commute_pmf)
   finally show ?case .
qed (simp)

lemma L_nths_Lxy:
  assumes "x\<in>set init" "y\<in>set init" "x\<noteq>y" "distinct init" 
  shows "map_pmf (\<lambda>l. nths l {index init x,index init y}) (Prob_Theory.bv (length init))
      = (Prob_Theory.bv (length (Lxy init {x,y})))"
proof -
  from assms(4) have setinit: "(index init) ` set init = {0..<length init}" 
  proof(induct init)
    case (Cons a as)
    with Cons have iH: "index as ` set as = {0..<length as}" by auto
    from Cons have 1:"(set as \<inter> {x. (a \<noteq> x)}) = set as" by fastforce
    have 2: "(\<lambda>a. Suc (index as a)) ` set as =
            (\<lambda>a. Suc a) ` ((index as) ` set as )" by auto
    show ?case
    apply(simp add: 1 2 iH) by auto
  qed simp

  have xy_le: "index init x<length init" "index init y<length init" using assms by auto
  have "map_pmf (\<lambda>l. nths l {index init x,index init y}) (Prob_Theory.bv (length init))
      = (Prob_Theory.bv (length (nths init {index init x,index init y})))"
        apply(rule L_nths)
        using assms(1,2) by auto
  moreover have "length (Lxy init {x,y}) = length (nths init {index init x,index init y})"
  proof -
    have "set (Lxy init {x,y}) = {x,y}" 
      using assms(1,2) by(simp add: Lxy_set_filter)
    moreover have "card {x,y} = 2" using assms(3) by auto
    moreover have "distinct (Lxy init {x,y})" using assms(4) by(simp add: Lxy_distinct)
    ultimately have 1: "length (Lxy init {x,y}) = 2" by(simp add: distinct_card[symmetric])
    have "set (nths init {index init x,index init y}) = {(init ! i) | i.  i < length init \<and> i \<in> {index init x,index init y}}" 
      using assms(1,2) by(simp add: set_nths)
    moreover have "card {(init ! i) | i.  i < length init \<and> i \<in> {index init x,index init y}} = 2"
    proof -
      have 1: "{(init ! i) | i.  i < length init \<and> i \<in> {index init x,index init y}} = {init ! index init x, init ! index init y}" using xy_le by blast
      also have "\<dots> = {x,y}" using nth_index assms(1,2) by auto 
      finally show ?thesis using assms(3) by auto
    qed
    moreover have "distinct (nths init {index init x,index init y})" using assms(4) by(simp)
    ultimately have 2: "length (nths init {index init x,index init y}) = 2" by(simp add: distinct_card[symmetric])
    show ?thesis using 1 2 by simp
  qed
  ultimately show ?thesis by simp
qed
  
lemma nths_map: "map f (nths xs S) = nths (map f xs) S"
apply(induct xs arbitrary: S) by(simp_all  add: nths_Cons)

lemma nths_empty: "(\<forall>i\<in>S. i\<ge>length xs) \<Longrightarrow> nths xs S = []"
proof -
  assume "(\<forall>i\<in>S. i\<ge>length xs)"
  then have "set (nths xs S) = {}" apply(simp add: set_nths) by force
  then show "nths xs S = []" by simp
qed


lemma nths_project': "i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> i<j
   \<Longrightarrow> nths xs {i,j} = [xs!i, xs!j]"
proof -
  assume il: "i < length xs" and jl: "j < length xs" and ij: "i<j"

  from il obtain a as where dec1: "a @ [xs!i] @ as = xs" 
           and "a = take i xs" "as=drop (Suc i) xs" 
           and length_a: "length a = i" and length_as: "length as = length xs - i - 1"using id_take_nth_drop by fastforce
  have "j\<ge>length (a @ [xs!i])" using length_a ij by auto
  then have "((a @ [xs!i]) @ as) ! j = as ! (j-length (a @ [xs ! i]))" using nth_append[where xs="a @ [xs!i]" and ys="as"]
    by(simp)
  then have xsj: "xs ! j = as ! (j-i-1)" using dec1 length_a by auto   
  have las: "(j-i-1) < length as" using length_as jl ij by simp
  obtain b c where dec2: "b @ [xs!j] @ c = as"
            and "b = take (j-i-1) as" "c=drop (Suc (j-i-1)) as"
            and length_b: "length b = j-i-1" using id_take_nth_drop[OF las] xsj by force
  have xs_dec: "a @ [xs!i] @ b @ [xs!j] @ c = xs" using dec1 dec2 by auto 
         
  have s2: "{k. (k + i \<in> {i, j})} = {0,j-i}"  using ij by force
  have s3: "{k. (k  + length [xs ! i] \<in> {0, j-i})} = {j-i-1}"  using ij by force
  have s4: "{k. (k  + length b \<in> {j-i-1})} = {0}"  using length_b by force
  have s5: "{k. (k  + length [xs!j] \<in> {0})} = {}" by force
  have l1: "nths a {i,j} = []"
    apply(rule nths_empty) using length_a ij by fastforce
  have l2: "nths b {j - Suc i} = []"
    apply(rule nths_empty) using length_b ij by fastforce
  have "nths ( a @ [xs!i] @ b @ [xs!j] @ c) {i,j} = [xs!i, xs!j]"
      apply(simp only: nths_append length_a s2 s3 s4 s5)
      by(simp add: l1 l2)
  then show "nths xs {i,j} = [xs!i, xs!j]" unfolding xs_dec .
qed

lemma nths_project:
  assumes  "i < length xs" "j < length xs" "i<j"
   shows "nths xs {i,j} ! 0 = xs ! i \<and> nths xs {i,j} ! 1 = xs ! j"
proof -
  from assms have "nths xs {i,j} = [xs!i, xs!j]" by(rule nths_project')
  then show ?thesis by simp
qed

lemma BIT_pairwise':
  assumes "set qs \<subseteq> set init"    
    "(x,y)\<in> {(x,y). x \<in> set init \<and> y\<in>set init \<and> x\<noteq>y}"
   and  xny:"x \<noteq> y" and dinit: "distinct init"
  shows "Pbefore_in x y BIT qs init = Pbefore_in x y BIT (Lxy qs {x,y}) (Lxy init {x,y})"                    
proof -
  from assms have xyininit: "{x, y} \<subseteq> set init" 
        and qsininit: "set qs \<subseteq> set init" by auto 

  have xyininit': "{y,x} \<subseteq> set init" using xyininit by auto
 
  have a: "x \<in> set init" "y\<in>set init" using assms by auto 

    { fix n
    have strong: "set qs \<subseteq> set init \<Longrightarrow>
      map_pmf (\<lambda>(l,(w,i)). (Lxy l {x,y},(nths w {index init x,index init y},Lxy init {x,y}))) (config_rand BIT init qs) =
      config_rand BIT (Lxy init {x, y}) (Lxy qs {x, y}) " (is "?inv \<Longrightarrow> ?L qs = ?R qs")
    proof (induct qs rule: rev_induct)
      case Nil 

      have " map_pmf (\<lambda>(l,(w,i)). (Lxy l {x,y},(nths w {index init x,index init y},Lxy init {x,y}))) (config_rand BIT init [])
          =  map_pmf (\<lambda>w. (Lxy init {x,y}, (w, Lxy init {x,y}))) (map_pmf (\<lambda>l. nths l {index init x,index init y}) (Prob_Theory.bv (length init)))"
              by(simp add: bind_return_pmf map_pmf_def bind_assoc_pmf split_def BIT_init_def)
      also have "\<dots> = map_pmf (\<lambda>w. (Lxy init {x,y}, (w, Lxy init {x,y}))) (Prob_Theory.bv (length (Lxy init {x, y})))" 
          using L_nths_Lxy[OF a xny dinit] by simp
      also have "\<dots> = config_rand BIT  (Lxy init {x, y}) (Lxy [] {x, y})"
          by(simp add: BIT_init_def bind_return_pmf bind_assoc_pmf map_pmf_def)
      finally show ?case . 
    next
      case (snoc q qs)
      then have qininit: "q \<in>  set init" 
            and qsininit: "set qs \<subseteq> set init" using qsininit by auto

      from  snoc(1)[OF qsininit] have iH: "?L qs = ?R qs" by (simp add: split_def)

      show ?case 
      proof (cases "q \<in> {x,y}")
        case True
        note whatisq=this
 
        have "?L (qs@[q]) =
         map_pmf (\<lambda>(l,(w,i)). (Lxy l {x,y},(nths w {index init x,index init y},Lxy init {x,y}))) (config_rand BIT init qs \<bind>
              (\<lambda>s. BIT_step s q \<bind> (\<lambda>(a, nis). return_pmf (step (fst s) q a, nis))))"
             by(simp add: split_def config'_rand_snoc) 
        also have "\<dots> =
        map_pmf (\<lambda>(l,(w,i)). (Lxy l {x,y}, (nths w {index init x,index init y},Lxy init {x,y}))) (config_rand BIT init qs) \<bind>
        (\<lambda>s.
            BIT_step s q \<bind>
            (\<lambda>(a, nis). return_pmf (step (fst s) q a, nis))) "
           apply(simp add: map_pmf_def split_def bind_return_pmf bind_assoc_pmf)
           apply(simp add: BIT_step_def bind_return_pmf)
        proof (rule bind_pmf_cong, goal_cases)
          case (2 z)
          let ?s = "fst z"
          let ?b = "fst (snd z)"

          from 2 have z: "set (?s) = set init" using config_rand_set[of BIT, simplified]  by metis
          with True have qLxy: "q \<in> set (Lxy (?s) {x, y})" using   xyininit by (simp add: Lxy_set_filter)
          from 2 have dz: "distinct (?s)" using dinit config_rand_distinct[of BIT, simplified] by metis
          then have dLxy: "distinct (Lxy (?s) {x, y})" using Lxy_distinct by auto

          from 2 have [simp]: "snd (snd z) = init" using config_n_init3[simplified]   by metis

          from 2 have [simp]: "length (fst (snd z)) = length init" using config_n_fst_init_length2[simplified] by metis 

          have indexinbounds: "index init x < length init" "index init y < length init"  using a by auto
          from a xny have indnot: "index init x \<noteq> index init y" by auto



          have f1: "index init x < length (fst (snd z))" using xyininit by auto
          have f2: "index init y < length (fst (snd z))" using xyininit by auto
          have 3: "index init x \<noteq> index init y" using xny xyininit by auto

          
          from dinit have dfil: "distinct (Lxy init {x,y})" by(rule Lxy_distinct)
          have Lxy_set: "set (Lxy init {x, y}) = {x,y}" apply(simp add: Lxy_set_filter) using xyininit by fast
          then have xLxy: "x\<in>set (Lxy init {x, y})" by auto
          have Lxy_length: "length (Lxy init {x, y}) = 2" using dfil Lxy_set xny distinct_card by fastforce 
          have 31:  "index (Lxy init {x, y}) x < 2" 
              and  32:  "index (Lxy init {x, y}) y < 2" using Lxy_set xyininit Lxy_length by auto
          have 33: "index (Lxy init {x, y}) x \<noteq> index (Lxy init {x,y}) y"
            using xny xLxy by auto
 
          have a1: "nths (flip (index init (q)) (fst (snd z))) {index init x,index init y}
                = flip (index (Lxy init {x,y}) (q)) (nths (fst (snd z)) {index init x,index init y})" (is "?A=?B")
          proof (simp only: list_eq_iff_nth_eq, goal_cases)
            case 1

            {assume ass: "index init x < index init y"
              then have "index (Lxy init {x,y}) x < index (Lxy init {x,y}) y"
                using Lxy_mono[OF xyininit dinit] before_in_def a(2) by force  
              with 31 32 have ix: "index (Lxy init {x,y}) x = 0"
                      and iy: "index (Lxy init {x,y}) y = 1" by auto


             have g1: "(nths (fst (snd z)) {index init x,index init y}) 
                        = [(fst (snd z)) ! index init x, (fst (snd z)) ! index init y]"
                        apply(rule nths_project')
                          using xyininit apply(simp)
                          using xyininit apply(simp)
                          by fact


            have "nths (flip (index init (q)) (fst (snd z))) {index init x,index init y}
                  = [flip (index init (q)) (fst (snd z))!index init x,
                        flip (index init (q)) (fst (snd z))!index init y]"
                        apply(rule nths_project')
                          using xyininit apply(simp)
                          using xyininit apply(simp)
                          by fact
            also have "\<dots> = flip (index (Lxy init {x,y}) (q)) [(fst (snd z)) ! index init x, (fst (snd z)) ! index init y]" 
              apply(cases "q=x")
                apply(simp add: ix) using flip_other[OF f2 f1 3] flip_itself[OF f1] apply(simp)
                using whatisq apply(simp add: iy) using flip_other[OF f1 f2 3[symmetric]] flip_itself[OF f2] by(simp)
            finally have "nths (flip (index init (q)) (fst (snd z))) {index init x,index init y}
                    = flip (index (Lxy init {x,y}) (q)) (nths (fst (snd z)) {index init x,index init y})" 
                    by(simp add: g1)
                          
            }note cas1=this
            have man: "{x,y} = {y,x}" by auto
            {assume "~ index init x < index init y"
              then have ass: "index init y < index init x" using 3 by auto
              then have "index (Lxy init {x,y}) y < index (Lxy init {x,y}) x"
                using Lxy_mono[OF xyininit' dinit] xyininit a(1) man by(simp add: before_in_def)
              with 31 32 have ix: "index (Lxy init {x,y}) x = 1"
                      and iy: "index (Lxy init {x,y}) y = 0" by auto


             have g1: "(nths (fst (snd z)) {index init y,index init x}) 
                        = [(fst (snd z)) ! index init y, (fst (snd z)) ! index init x]"
                        apply(rule nths_project')
                          using xyininit apply(simp)
                          using xyininit apply(simp)
                          by fact

            have man2: "{index init x,index init y} = {index init y,index init x}" by auto
            have "nths (flip (index init (q)) (fst (snd z))) {index init y,index init x}
                  = [flip (index init (q)) (fst (snd z))!index init y,
                        flip (index init (q)) (fst (snd z))!index init x]"
                        apply(rule nths_project')
                          using xyininit apply(simp)
                          using xyininit apply(simp)
                          by fact
            also have "\<dots> = flip (index (Lxy init {x,y}) (q)) [(fst (snd z)) ! index init y, (fst (snd z)) ! index init x]" 
              apply(cases "q=x")
                apply(simp add: ix) using flip_other[OF f2 f1 3] flip_itself[OF f1] apply(simp)
                using whatisq apply(simp add: iy) using flip_other[OF f1 f2 3[symmetric]] flip_itself[OF f2] by(simp)
            finally have "nths (flip (index init (q)) (fst (snd z))) {index init y,index init x}
                    = flip (index (Lxy init {x,y}) (q)) (nths (fst (snd z)) {index init y,index init x})" 
                    by(simp add: g1)
            then have "nths (flip (index init (q)) (fst (snd z))) {index init x,index init y}
                    = flip (index (Lxy init {x,y}) (q)) (nths (fst (snd z)) {index init x,index init y})" 
                    using man2 by auto                          
            } note cas2=this

            from cas1 cas2 3 show ?case by metis 
          qed

          have a: "nths (fst (snd z)) {index init x, index init y} ! (index (Lxy init {x,y}) (q))
                    = fst (snd z) ! (index init (q))"
          proof -
            from 31 32  33have ca: "(index (Lxy init {x,y}) x = 0 \<and> index (Lxy init {x,y}) y = 1)
                    \<or> (index (Lxy init {x,y}) x = 1 \<and> index (Lxy init {x,y}) y = 0)" by force
            show ?thesis
            proof (cases "index (Lxy init {x,y}) x = 0")
              case True

              from True ca have y1: "index (Lxy init {x,y}) y = 1" by auto
              with True have "index (Lxy init {x,y}) x < index (Lxy init {x,y}) y" by auto
              then have xy: "index init x < index init y" using dinit dfil Lxy_mono 
                      using "32" before_in_def Lxy_length xyininit by fastforce 
                  

              have 4: " {index init y, index init x} =  {index init x, index init y}" by auto

              have "nths (fst (snd z)) {index init x, index init y} ! index (Lxy init {x,y}) x = (fst (snd z)) ! index init x"
                       "nths (fst (snd z)) {index init x, index init y} ! index (Lxy init {x,y}) y = (fst (snd z)) ! index init y"
                       unfolding True y1 
                          by (simp_all only: nths_project[OF f1 f2 xy])  
              with whatisq show ?thesis by auto
           next
              case False
              with ca have x1: "index (Lxy init {x,y}) x = 1" by auto
              from dinit have dfil: "distinct (Lxy init {x,y})" by(rule Lxy_distinct)

              from x1 ca have y1: "index (Lxy init {x,y}) y = 0" by auto
              with x1 have "index (Lxy init {x,y}) y < index (Lxy init {x,y}) x" by auto
              then have xy: "index init y < index init x" using dinit dfil Lxy_mono 
                      using "32" before_in_def Lxy_length xyininit by (metis a(2) indnot linorder_neqE_nat not_less0 y1) 
                  

              have 4: " {index init y, index init x} =  {index init x, index init y}" by auto
 
              have "nths (?b) {index init x, index init y} ! index (Lxy init {x,y}) x = (?b) ! index init x"
                       "nths (?b) {index init x, index init y} ! index (Lxy init {x,y}) y = (?b) ! index init y"
                       unfolding x1 y1 
                        using 4 nths_project[OF  f2 f1 xy]
                          by simp_all  
              with whatisq show ?thesis by auto
           qed
         qed


          have b: "Lxy (mtf2 (length ?s) (q) ?s) {x, y} 
                =  mtf2 (length (Lxy ?s {x, y})) (q) (Lxy ?s {x, y})" (is "?A = ?B")
          proof -
                have sA: "set ?A = {x,y}" using z xyininit by(simp add: Lxy_set_filter)
                then have xlxymA: "x \<in> set ?A"
                      and ylxymA: "y \<in> set ?A" by auto
                have dA: "distinct ?A" apply(rule Lxy_distinct) by(simp add: dz)
                have lA: "length ?A = 2" using xny sA dA distinct_card by fastforce 
                from lA ylxymA have yindA: "index ?A y < 2" by auto
                from lA xlxymA have xindA: "index ?A x < 2" by auto
                have geA: "{x,y} \<subseteq> set (mtf2 (length ?s) (q) ?s)" using xyininit z by auto
                have geA': "{y,x} \<subseteq> set (mtf2 (length ?s) (q) (?s))" using xyininit z by auto
                have man: "{y,x} = {x,y}" by auto

                have sB: "set ?B = {x,y}" using z xyininit by(simp add: Lxy_set_filter)
                then have xlxymB: "x \<in> set ?B"
                  and ylxymB: "y \<in> set ?B" by auto
                have dB: "distinct ?B" apply(simp) apply(rule Lxy_distinct) by(simp add: dz)
                have lB: "length ?B = 2" using xny sB dB distinct_card by fastforce 
                from lB ylxymB have yindB: "index ?B y < 2" by auto
                from lB xlxymB have xindB: "index ?B x < 2" by auto
                
                show ?thesis
                proof (cases "q = x")                
                  case True
                  then have xby: "x < y in (mtf2 (length (?s)) (q) (?s))"
                    apply(simp)
                          apply(rule mtf2_moves_to_front''[simplified])
                            using z xyininit xny by(simp_all add: dz)
                  then have "x < y in ?A" using Lxy_mono[OF geA] dz by(auto)
                  then have "index ?A x < index ?A y" unfolding before_in_def by auto
                  then have in1: "index ?A x = 0"
                          and in2: "index ?A y = 1"  using yindA by auto
                  have "?A = [?A!0,?A!1]" 
                          apply(simp only: list_eq_iff_nth_eq)
                            apply(auto simp: lA) apply(case_tac i) by(auto)
                  also have "\<dots> = [?A!index ?A x, ?A!index ?A y]" by(simp only: in1 in2)
                  also have "\<dots> = [x,y]" using xlxymA ylxymA  by simp    
                  finally have end1: "?A  = [x,y]" .
                  
                  have "x < y in ?B"
                    using True apply(simp)
                          apply(rule mtf2_moves_to_front''[simplified])
                            using z xyininit xny by(simp_all add: Lxy_distinct dz Lxy_set_filter)
                  then have "index ?B x < index ?B y"
                            unfolding before_in_def by auto
                  then have in1: "index ?B x = 0"
                          and in2: "index ?B y = 1"
                            using yindB by auto
  
                  have "?B = [?B!0, ?B!1]" 
                          apply(simp only: list_eq_iff_nth_eq)
                            apply(simp only: lB)
                            apply(auto) apply(case_tac i) by(auto)
                  also have "\<dots> = [?B!index ?B x,  ?B!index ?B y]"
                                 by(simp only: in1 in2)
                  also have "\<dots> = [x,y]" using xlxymB ylxymB  by simp    
                  finally have end2: "?B = [x,y]" .
  
                  then show "?A = ?B " using end1 end2 by simp
              next             
                  case False
                  with whatisq have qsy: "q=y" by simp
                  then have xby: "y < x in (mtf2 (length (?s)) (q) (?s))"
                    apply(simp)
                          apply(rule mtf2_moves_to_front''[simplified])
                            using z xyininit xny by(simp_all add: dz)
                  then have "y < x in ?A" using Lxy_mono[OF geA'] man dz by auto
                  then have "index ?A y < index ?A x" unfolding before_in_def by auto
                  then have in1: "index ?A y = 0"
                          and in2: "index ?A x = 1"  using xindA by auto
                  have "?A = [?A!0,?A!1]" 
                          apply(simp only: list_eq_iff_nth_eq)
                            apply(auto simp: lA) apply(case_tac i) by(auto)
                  also have "\<dots> = [?A!index ?A y, ?A!index ?A x]" by(simp only: in1 in2)
                  also have "\<dots> = [y,x]" using xlxymA ylxymA  by simp    
                  finally have end1: "?A  = [y,x]" .
                  
                  have "y < x in ?B"
                    using qsy apply(simp)
                          apply(rule mtf2_moves_to_front''[simplified])
                            using z xyininit xny by(simp_all add: Lxy_distinct dz Lxy_set_filter)
                  then have "index ?B y < index ?B x"
                            unfolding before_in_def by auto
                  then have in1: "index ?B y = 0"
                          and in2: "index ?B x = 1"
                            using xindB by auto
  
                  have "?B = [?B!0, ?B!1]" 
                          apply(simp only: list_eq_iff_nth_eq)
                            apply(simp only: lB)
                            apply(auto) apply(case_tac i) by(auto)
                  also have "\<dots> = [?B!index ?B y,  ?B!index ?B x]"
                                 by(simp only: in1 in2)
                  also have "\<dots> = [y,x]" using xlxymB ylxymB  by(simp )    
                  finally have end2: "?B = [y,x]" .
  
                  then show "?A = ?B " using end1 end2 by simp
              qed  
           qed 
          
          have a2: " Lxy (step (?s) (q) (if ?b ! (index init (q)) then 0 else length (?s), [])) {x, y}
              = step (Lxy (?s) {x, y}) (q) (if nths (?b) {index init x, index init y} ! (index (Lxy init {x,y}) (q)) 
                              then 0 
                              else length (Lxy (?s) {x, y}), [])"
               apply(auto simp add: a step_def) by(simp add: b)
 

           show ?case using a1 a2 by(simp)
        qed simp 
        also have "\<dots> = ?R (qs@[q])"
          using True apply(simp add: Lxy_snoc take_Suc_conv_app_nth config'_rand_snoc)  
          using iH by(simp add: split_def ) 
        finally show ?thesis .
      next
        case False
        then have qnx: "(q) \<noteq> x" and qny: "(q) \<noteq> y" by auto

        let ?proj="(\<lambda>a. (Lxy (fst a) {x, y}, (nths (fst (snd a)) {index init x, index init y}, Lxy init {x, y})))"
             
        have "map_pmf ?proj (config_rand BIT init (qs@[q]))
             = map_pmf ?proj (config_rand (BIT_init, BIT_step) init qs
                \<bind> (\<lambda>p. BIT_step p (q) \<bind> (\<lambda>pa. return_pmf (step (fst p) (q) (fst pa), snd pa)))) "
               by (simp add: split_def take_Suc_conv_app_nth config'_rand_snoc)
        also have "\<dots> = map_pmf ?proj (config_rand (BIT_init, BIT_step) init qs)" 
            apply(simp add: map_pmf_def bind_assoc_pmf bind_return_pmf BIT_step_def)
            proof (rule bind_pmf_cong, goal_cases)
              case (2 z)
              let ?s = "fst z"
              let ?m = "snd (snd z)"
              let ?b = "fst (snd z)"

              from 2 have sf_init: "?m = init" using config_n_init3 by auto

              from 2 have ff_len: "length (?b) = length init" using config_n_fst_init_length2 by auto
              
              have ff_ix: "index init x < length (?b)" unfolding ff_len using a(1) by auto
              have ff_iy: "index init y < length (?b)" unfolding ff_len using a(2) by auto
              have ff_q: "index init (q) < length (?b)" unfolding ff_len using qininit by auto
              have iq_ix: "index init (q) \<noteq> index init x" using a(1) qnx by auto
              have iq_iy: "index init (q) \<noteq> index init y" using a(2) qny by auto
              have ix_iy: "index init x \<noteq> index init y" using a(2) xny by auto

              from 2 have s_set[simp]: "set (?s) = set init" using config_rand_set by force
              have s_xin: "x\<in>set (?s)" using a(1) by simp
              have s_yin: "y\<in>set (?s)" using a(2) by simp
              from 2 have s_dist: "distinct (?s)" using config_rand_distinct dinit by force
              have s_qin: "q \<in> set (?s)" using qininit by simp


              have fstfst: "nths (flip (index ?m (q)) (?b))
              {index init x, index init y}
                  = nths (?b) {index init x, index init y}" (is "nths ?A ?I = nths ?B ?I")
              proof (cases "index init x < index init y")
                case True
                have "nths ?A ?I = [?A!index init x, ?A!index init y]"
                      apply(rule nths_project')
                        by(simp_all add: ff_ix ff_iy True)
                also have "\<dots> = [?B!index init x, ?B!index init y]"
                  unfolding sf_init using flip_other ff_ix ff_iy ff_q iq_ix iq_iy by auto
                also have "\<dots> = nths ?B ?I"
                      apply(rule nths_project'[symmetric])
                        by(simp_all add: ff_ix ff_iy True)
                finally show ?thesis .
              next
                case False
                then have yx: "index init y < index init x" using ix_iy by auto
                have man: "?I =  {index init y, index init x}" by auto
                have "nths ?A {index init y, index init x}  = [?A!index init y, ?A!index init x]"
                      apply(rule nths_project')
                        by(simp_all add: ff_ix ff_iy yx)
                also have "\<dots> = [?B!index init y, ?B!index init x]"
                  unfolding sf_init using flip_other ff_ix ff_iy ff_q iq_ix iq_iy by auto
                also have "\<dots> = nths ?B {index init y, index init x}"
                      apply(rule nths_project'[symmetric])
                        by(simp_all add: ff_ix ff_iy yx)
                finally show ?thesis by(simp add: man)
              qed


              have snd: "Lxy (step (?s) (q)
                  (if ?b ! index ?m (q) then 0 else length (?s),
                   [])) {x, y} = Lxy (?s) {x, y}" (is "Lxy ?A {x,y} = Lxy ?B {x,y}")
              proof (cases "x < y in ?B")
                case True
                note B=this
                then have A: "x<y in ?A" apply(auto simp add: step_def split_def)
                  apply(rule x_stays_before_y_if_y_not_moved_to_front)
                    by(simp_all add: a s_dist qny[symmetric] qininit)

                have "Lxy ?A {x,y} = [x,y]"
                  apply(rule Lxy_project)
                    by(simp_all add: xny set_step distinct_step A s_dist a)
                also have "... = Lxy ?B {x,y}"
                  apply(rule Lxy_project[symmetric])
                    by(simp_all add: xny B s_dist a)
                finally show ?thesis .
              next
                case False
                then have B: "y < x in ?B" using not_before_in[OF s_xin s_yin] xny by simp
                then have A: "y < x in ?A " apply(auto simp add: step_def split_def)
                  apply(rule x_stays_before_y_if_y_not_moved_to_front)
                    by(simp_all add: a s_dist qnx[symmetric] qininit)
                have man: "{x,y} = {y,x}" by auto
                have "Lxy ?A {y,x} = [y,x]"
                  apply(rule Lxy_project)
                    by(simp_all add: xny[symmetric] set_step distinct_step A s_dist a)
                also have "... = Lxy ?B {y,x}"
                  apply(rule Lxy_project[symmetric])
                    by(simp_all add: xny[symmetric] B s_dist a)
                finally show ?thesis using man by auto
              qed
 
              show ?case by(simp add: fstfst snd)
            qed simp
        also have "\<dots> = config_rand BIT (Lxy init {x, y}) (Lxy qs {x, y})"
          using iH by (auto simp: split_def)
        also have "\<dots> = ?R (qs@[q])"
          using False by(simp add: Lxy_snoc)
        finally show ?thesis by (simp add: split_def)
      qed 
    qed
    } note strong=this

  { 
    fix n::nat 
    have "Pbefore_in x y BIT qs init = 
        map_pmf (\<lambda>p. x < y in fst p)
            (map_pmf (\<lambda>(l, (w, i)). (Lxy l {x, y}, (nths w {index init x, index init y}, Lxy init {x, y})))
                  (config_rand BIT init qs))" 
                  unfolding Pbefore_in_def apply(simp add: map_pmf_def bind_return_pmf bind_assoc_pmf split_def)
                  apply(rule bind_pmf_cong)
                    apply(simp)
                    proof (goal_cases)
                      case (1 z)
                      let ?s = "fst z"
                      from 1 have u: "set (?s) = set init" using config_rand[of BIT, simplified] by metis
                      from 1 have v: "distinct (?s)" using dinit config_rand[of BIT, simplified] by metis
                      have "(x < y in ?s) = (x < y in Lxy (?s) {x, y})"
                        apply(rule Lxy_mono)
                          using u xyininit apply(simp)
                          using v by simp
                      then show ?case by simp
                    qed
     also have "\<dots> = map_pmf (\<lambda>p. x < y in fst p) (config_rand BIT (Lxy init {x, y}) (Lxy qs {x, y}))"
        apply(subst strong) using assms by simp_all
     also have "\<dots> = Pbefore_in x y BIT (Lxy qs {x, y}) (Lxy init {x, y})" unfolding Pbefore_in_def by simp
     finally have "Pbefore_in x y BIT qs init =
        Pbefore_in x y BIT (Lxy qs {x, y}) (Lxy init {x, y})" .      
  
  } note fine=this

  with assms show ?thesis by simp
qed
        

theorem BIT_pairwise: "pairwise BIT"
apply(rule pairwise_property_lemma)
  apply(rule BIT_pairwise') 
    by(simp_all add: BIT_step_def)


end
