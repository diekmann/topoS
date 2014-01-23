theory datatype_DomainHierarchy
imports Main "~~/src/HOL/Lattice/CompleteLattice"
begin
(* TODO: Lattices.thy in ~~/src/HOL/ might be better *)


section {* Domain Hierarchy for organisational structure of Networks *}



datatype domainName =  Dept "string" domainName (infixr "--" 65) |
    Leaf --"leaf of the tree, end of all domainNames" |
    Unassigned

    text {*Example: the CoffeeMachine of I8 *}
    value "''i8''--''CoffeeMachine''--Leaf"


datatype domainTree = Department 
    "string"  --"division"
    "domainTree list"  --"sub divisions"


fun hierarchy_next :: "domainTree list \<Rightarrow> domainName \<Rightarrow> domainTree option" where
  "hierarchy_next [] _ = None" |
  "hierarchy_next (s#ss) Unassigned = None" | 
  "hierarchy_next (s#ss) Leaf = None" | 
  "hierarchy_next ((Department d ds)#ss) (Dept n ns) = (if d=n then Some (Department d ds) else hierarchy_next ss (Dept n ns))"

    text {*Examples: *}
    value "hierarchy_next [Department ''i20'' [], Department ''i8'' [Department ''CoffeeMachine'' [], Department ''TeaMachine'' []]] 
        (''i8''--Leaf)"
    value "hierarchy_next [Department ''i20'' [], Department ''i8'' [Department ''CoffeeMachine'' [], Department ''TeaMachine'' []]] 
        (''i8''--''whatsoever''--Leaf)"
    value "hierarchy_next [Department ''i20'' [], Department ''i8'' [Department ''CoffeeMachine'' [], Department ''TeaMachine'' []]] 
        Unassigned"
    value "hierarchy_next [Department ''i20'' [], Department ''i8'' [Department ''CoffeeMachine'' [], Department ''TeaMachine'' []]] 
        (''i0''--Unassigned)"

text {* Does a given domainName match the specified tree structure? *}
fun valid_hierarchy_pos :: "domainTree \<Rightarrow> domainName \<Rightarrow> bool" where
  "valid_hierarchy_pos (Department d ds) Unassigned = True" |
  "valid_hierarchy_pos (Department d ds) Leaf = False" | (* TODO: set this to True for unique default. Now Leaf is a VALID default_node_property! *)
  "valid_hierarchy_pos (Department d ds) (Dept n Leaf) = (d=n)" |
  "valid_hierarchy_pos (Department d ds) (Dept n ns) = (n=d \<and> 
    (case hierarchy_next ds ns of 
      None \<Rightarrow> False |
      Some t \<Rightarrow> valid_hierarchy_pos t ns))"


    text {* Examples: *}
    value "valid_hierarchy_pos (Department ''TUM'' []) Leaf"
    value "valid_hierarchy_pos (Department ''TUM'' []) Unassigned"
    value "valid_hierarchy_pos (Department ''TUM'' []) (''TUM''--Leaf)"
    value "valid_hierarchy_pos (Department ''TUM'' []) (''TUM''--Unassigned)"
    value "valid_hierarchy_pos (Department ''TUM'' []) (''TUM''--''facilityManagement''--Leaf)"
    value "valid_hierarchy_pos (Department ''TUM'' []) (''LMU''--Leaf)"
    value "valid_hierarchy_pos (Department ''TUM'' [Department ''i8'' [], (Department ''i20'' [])])  (''TUM''--Leaf)"
    value "valid_hierarchy_pos (Department ''TUM'' [Department ''i8'' [], Department ''i20'' []])  (''TUM''--''i8''--Leaf)"
    value "valid_hierarchy_pos 
        (Department ''TUM'' [
           Department ''i8'' [
            Department ''CoffeeMachine'' [],
            Department ''TeaMachine'' []
           ], 
           Department ''i20'' []
        ]) 
        (''TUM''--''i8''--''CoffeeMachine''--Leaf)"
    value "valid_hierarchy_pos (Department ''TUM'' [Department ''i8'' [Department ''CoffeeMachine'' [], Department ''TeaMachine'' []], Department ''i20'' []]) 
        (''TUM''--''i8''--''CleanKitchen''--Leaf)"

(* TODO: is a security class lattice [Den76] *)
instantiation domainName :: order (* preorder *)
begin
  print_context
  
  fun less_eq_domainName :: "domainName \<Rightarrow> domainName \<Rightarrow> bool" where
    "Unassigned \<le> Unassigned = True" |
    "Unassigned \<le> Leaf = True" |
    "Leaf \<le> Unassigned = False" |
    "Unassigned \<le> (Dept _ _) = True" |
    "(Dept _ _) \<le> Unassigned = False" |
    "Leaf \<le> (Dept _ _) = False" |
    "(Dept _ _) \<le> Leaf = True" |
    "Leaf \<le> Leaf = True" |
    "(Dept n1 n1s) \<le> (Dept n2 n2s) = (n1=n2 \<and> n1s \<le> n2s)"
  
  fun less_domainName :: "domainName \<Rightarrow> domainName \<Rightarrow> bool" where
    "Unassigned < Unassigned = False" |
    "Leaf < Leaf = False" |
    "Unassigned < Leaf = True" |
    "Leaf < Unassigned = False" |
    "Unassigned < (Dept _ _) = True" |
    "(Dept _ _) < Unassigned = False" |
    "Leaf < (Dept _ _) = False" |
    "(Dept _ _) < Leaf = True" |
    "(Dept n1 n1s) < (Dept n2 n2s) = (n1=n2 \<and> n1s < n2s)"
  
  lemma Unassigned_bot: "Unassigned \<le> a"
    apply(case_tac a)
    by(simp_all)

 lemma Unassigned_bot_Unique: "a \<le> Unassigned \<Longrightarrow> a = Unassigned"
    apply(case_tac a)
    by(simp_all)

  lemma Leaf_Top: "a \<le> Leaf"
    apply(case_tac a)
    by(simp_all)

  lemma Leaf_Top_Unique: "Leaf \<le> a \<Longrightarrow> a = Leaf"
    apply(case_tac a)
    by(simp_all)

  lemma uncomparable_inf_is_bot: "n1 \<noteq> n2 \<Longrightarrow> z \<le> n1 -- n1s \<and> z \<le> n2 -- n2s \<Longrightarrow> z = Unassigned"
    apply(case_tac z)
    apply(simp_all)
    by fast

  lemma uncomparable_sup_is_Top: "n1 \<noteq> n2 \<Longrightarrow> n1 -- x \<le> z \<Longrightarrow> n2 -- y \<le> z \<Longrightarrow> z = Leaf"
    apply(case_tac z)
    by(simp_all)


  lemma prepend_domain: "a \<le> b \<Longrightarrow> x--a \<le> x--b"
    by(simp)
  
  lemma less_eq_refl: "(x::domainName) \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z "
    proof(induction x arbitrary: y z)
      case Unassigned thus ?case by(simp add:Unassigned_bot)
    next
      case (Dept x xn)
        from Dept have yUnass: "y = Unassigned \<Longrightarrow> x -- xn \<le> z" by simp
        from Dept have "\<And> y' yn'. y = (Dept y' yn') \<Longrightarrow> x=y' \<and> xn \<le> yn'" by simp
        from Dept have zDept: "\<And> y' yn'. y = (Dept y' yn') \<Longrightarrow> (\<exists> z' zn'. z=(Dept z' zn')) \<or> z = Leaf" 
          apply(case_tac z) by simp_all
        from Dept have DeptX1: "\<And> y z. xn \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> xn \<le> z" and DeptX2: "x -- xn \<le> y" and DeptX3: "y \<le> z" by auto
        show ?case
          proof(cases y)
            case Unassigned thus "x -- xn \<le> z" using yUnass by simp
          next
            case Leaf thus "x -- xn \<le> z" using yUnass by (metis DeptX3 Leaf_Top Leaf_Top_Unique)
          next
            case (Dept y' yn')
              show "x -- xn \<le> z"
               proof(cases "z=Leaf")
                  assume "z=Leaf"
                  thus "x -- xn \<le> z" using Leaf_Top by auto
                next
                  assume "z \<noteq> Leaf"
                  from Dept this zDept obtain z' zn' where z'Prop: "z=(Dept z' zn')" by blast
                  from this Dept DeptX1 have C1: "\<And> y z. xn \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> xn \<le> z" by auto
                  from Dept DeptX2 have "x -- xn \<le> y'--yn'" by auto
                  hence "x=y'" and "xn \<le> yn'" by auto
                  from Dept z'Prop DeptX3 have yLEQz: "y' -- yn' \<le> z'--zn'" by auto
                  hence "y'=z'" and "yn' \<le> zn'" by auto
                  from C1 `x=y'` `y'=z'` yLEQz have "xn \<le> x--yn' \<Longrightarrow> xn \<le> z'--zn'" by auto
                  from DeptX2 Dept have "x -- xn \<le> y' -- yn'" by auto
                  hence "xn \<le> yn'" by auto
        
                  from C1 `xn \<le> yn'` `yn' \<le> zn'` have "xn \<le> zn'" by auto
                  from this `x=y'` `y'=z'` have "x -- xn \<le> z'--zn'" by auto
                  thus "x -- xn \<le> z" using z'Prop by auto
              qed
          qed
       next
       case Leaf from this Leaf_Top show ?case
        by (metis domainName.exhaust less_eq_domainName.simps(3) less_eq_domainName.simps(6))
    qed

instance
  proof
    fix x y ::domainName
    show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
      apply(induction x arbitrary: y)
      apply(rename_tac x nx y)
      defer
      apply(case_tac y)
       apply simp
       apply simp
       apply simp
      apply(case_tac y)
       apply simp
       apply simp
       apply simp
      apply(case_tac y)
      defer
      apply simp
      apply simp
      apply(rename_tac y' ny')
      apply simp
      apply(case_tac "x=y'")
      defer
       apply simp
      by simp
  next
    fix x::domainName
    show "x \<le> x"
      using[[show_types]] apply(induction x)
      by simp_all
  next
    fix x y z :: domainName
    show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z " apply (rule less_eq_refl) apply simp_all done
  next
    fix x y ::domainName
    show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
      apply(induction x arbitrary: y)
      apply(rename_tac x nx y)
      defer
      apply(case_tac y)
       apply simp
       apply simp
       apply simp
      apply(case_tac y)
       apply simp
       apply simp
       apply simp
      apply(case_tac y)
      defer
      apply simp
      apply simp
      apply(rename_tac y' ny')
      by simp
qed

end

instantiation domainName :: Orderings.bot
begin
  definition bot_domainName where "Orderings.bot \<equiv> Unassigned"
  instance
    by intro_classes
    (*unfolding bot_domainName_def
    by(rule Unassigned_bot) isabelle2013*)
end

instantiation domainName :: Orderings.top
begin
  definition top_domainName where "Orderings.top \<equiv> Leaf"
  instance
    by intro_classes
    (*unfolding top_domainName_def
    by(rule Leaf_Top) isabelle2013*)
end

    value "(''TUM''--''BLUBB''--Leaf) \<le> (''TUM''--Leaf)"
    value "Unassigned \<le> (''TUM''--Leaf)"

    value "(''TUM''--Leaf) \<le> (''TUM''--''i8''--Leaf)"
      value "valid_hierarchy_pos (Department ''TUM'' [Department ''i8'' [], Department ''i20'' []]) (''TUM''--''i8''--Leaf)"
    
    value "(''TUM''--Leaf) \<le> Leaf"
      value "valid_hierarchy_pos (Department ''TUM'' [Department ''i8'' [], Department ''i20'' []]) (Leaf)"

    value "(''TUM''--''BLUBB''--Unassigned) \<le> (''TUM''--Unassigned)"
      value "valid_hierarchy_pos (Department ''TUM'' [Department ''i8'' [], Department ''i20'' []]) (''TUM''--Unassigned)"

    value "(''TUM''--''BLUBB''--Leaf) \<le> (''TUM''--Unassigned)"
      value "valid_hierarchy_pos (Department ''TUM'' [Department ''i8'' [], Department ''i20'' []]) (''TUM''--Unassigned)"

    value "(''TUM''--''BLUBB''--Unassigned) \<le> (''TUM''--Leaf)"
      value "valid_hierarchy_pos (Department ''TUM'' [Department ''i8'' [], Department ''i20'' []]) (''TUM''--''BLUBB''--Unassigned)"

    value "Unassigned \<le> (''TUM''--Unassigned)"
      value "valid_hierarchy_pos (Department ''TUM'' [Department ''i8'' [], Department ''i20'' []]) (''TUM''--Unassigned)"

    value "Leaf \<le> (''TUM''--Unassigned)"
      value "valid_hierarchy_pos (Department ''TUM'' [Department ''i8'' [], Department ''i20'' []]) (''TUM''--Unassigned)"

    value "Leaf \<le> (''TUM''--Leaf)"
      value "valid_hierarchy_pos (Department ''TUM'' [Department ''i8'' [], Department ''i20'' []]) (''TUM''--Leaf)"

    value "(''TUM''--Unassigned) \<le> (''TUM''--''BLUBB''--Unassigned)"
      value "valid_hierarchy_pos (Department ''TUM'' [Department ''i8'' [], Department ''i20'' []]) (''TUM''--''BLUBB''--Unassigned)"

    value "(''TUM''--''i8''--Leaf) \<le> (''TUM''--Leaf)"
      value "valid_hierarchy_pos (Department ''TUM'' [Department ''i8'' [], Department ''i20'' []]) (''TUM''--''i8''--Leaf)"

    value "(''TUM''--''BLUBB''--Leaf) \<le> (''X''--''TUM''--''BLUBB''--Leaf)"
      value "valid_hierarchy_pos (Department ''TUM'' [Department ''i8'' [], Department ''i20'' []]) (''X''--''TUM''--''BLUBB''--Leaf)"

      (* Text examples*)
    value "(''TUM''--''i8''--''CoffeeMachine''--Leaf) \<le> (''TUM''--''i8''--Leaf)"
    value "(Unassigned) \<le> (''TUM''--''i8''--Leaf)"
    value "(''TUM''--''i8''--Leaf) \<le> (''TUM''--''i8''--Leaf)"
    value "(''TUM''--''i8''--''CoffeeMachine''--Leaf) \<le> (''TUM''--Leaf)"
    value "(''TUM''--''i8''--''CoffeeMachine''--Leaf) \<le> (Leaf)"
    value "\<not> (''TUM''--''i8''--Leaf) \<le> (''TUM''--''i20''--Leaf)"
    value "\<not> (''TUM''--''i20''--Leaf) \<le> (''TUM''--''i8''--Leaf)"



  section {*Security Lattice*}
    instantiation domainName :: partial_order
    begin
      print_context
      definition leq_domainName :: "domainName \<Rightarrow> domainName \<Rightarrow> bool" (* \<sqsubseteq> *)
        where "leq_domainName A B \<equiv> A \<le> B"
    instance
      apply intro_classes
      unfolding leq_domainName_def
      by (simp_all)
    end

    lemma "is_Inf {Unassigned, Leaf} Unassigned"
      unfolding is_Inf_def
      apply simp
      unfolding leq_domainName_def
      by simp
    
    text {*The infinum of two elements: *}
    fun DH_inf :: "domainName \<Rightarrow> domainName \<Rightarrow> domainName" where
      "DH_inf Unassigned _ = Unassigned" | 
      "DH_inf _ Unassigned = Unassigned" | 
      "DH_inf a Leaf = a" | 
      "DH_inf Leaf a = a" |
      "DH_inf (n1--n1s) (n2--n2s) = (if n1=n2 then n1--(DH_inf n1s n2s) else Unassigned)" 
      
    lemma is_inf_prepend_domain: "is_inf x y (DH_inf x y) \<Longrightarrow> is_inf (x1--x) (x1--y) (x1--(DH_inf x y))"
      unfolding is_inf_def
      unfolding leq_domainName_def
      apply (simp)
      apply clarify
      apply(case_tac z)
      by(simp_all)

    lemma DH_inf_Un: "is_inf Unassigned y Unassigned"
      by(case_tac y, simp_all add: is_inf_def leq_domainName_def)
    lemma DH_infUn: "is_inf x Unassigned Unassigned"
      by(case_tac x, simp_all add: is_inf_def leq_domainName_def)
    lemma DH_inf_Le: "is_inf x Leaf x"
      by(case_tac x, simp_all add: is_inf_def leq_domainName_def)
    lemma DH_infLe: "is_inf Leaf x x"
      by(case_tac x, simp_all add: is_inf_def leq_domainName_def)
    lemma DH_infLeSimp: "is_inf Leaf y (DH_inf Leaf y)"
      by(case_tac y, simp_all add: is_inf_def leq_domainName_def)
    lemma DH_inf_in_inf: "is_inf x y (DH_inf x y)"
      apply(induction x arbitrary: y)
       apply (simp_all add: DH_inf_Un DH_infUn DH_inf_Le DH_infLe DH_infLeSimp)
      apply(rename_tac xs x y)
      apply(case_tac y)
       apply (simp_all add: DH_inf_Un DH_infUn DH_inf_Le DH_infLe DH_infLeSimp)
      apply(rename_tac y2 y2s)
      apply(rule conjI)
      apply(clarify)
      apply(subgoal_tac "is_inf x y2s (DH_inf x y2s)")
       apply(simp add:is_inf_prepend_domain)
       apply force
      unfolding is_inf_def
      unfolding leq_domainName_def
      apply(clarify)
      apply(simp add: Unassigned_bot)
      apply(clarify)
      apply(subgoal_tac "z = Unassigned")
       apply(simp)
      apply(insert uncomparable_inf_is_bot)[1]
       apply metis
      done
    
    lemma DH_inf_commute: "DH_inf x y = DH_inf y x"
      apply(induction x arbitrary: y)
       apply (simp_all)
      apply(case_tac y)
       apply (simp_all)
      apply(case_tac y)
       apply (simp_all)
      apply(case_tac y)
      by (simp_all)
    
    fun DH_sup :: "domainName \<Rightarrow> domainName \<Rightarrow> domainName" where
      "DH_sup Unassigned a = a" | 
      "DH_sup a Unassigned = a" | 
      "DH_sup _ Leaf = Leaf" | 
      "DH_sup Leaf _ = Leaf" |
      "DH_sup (n1--n1s) (n2--n2s) = (if n1=n2 then n1--(DH_sup n1s n2s) else Leaf)" 
    
    lemma is_sup_prepend_domain: "is_sup x y (DH_sup x y) \<Longrightarrow> is_sup (x1--x) (x1--y) (x1--(DH_sup x y))"
      unfolding is_sup_def
      unfolding leq_domainName_def
      apply (simp)
      apply clarify
      apply(case_tac z)
      by(simp_all)

    lemma DH_sup_Un: "is_sup Unassigned y y"
      by(case_tac y, simp_all add: is_sup_def leq_domainName_def)
    lemma DH_supUn: "is_sup x Unassigned x"
      by(case_tac x, simp_all add: is_sup_def leq_domainName_def)
    lemma DH_sup_Le: "is_sup x Leaf Leaf"
      by(case_tac x, simp_all add: is_sup_def leq_domainName_def)
    lemma DH_supLe: "is_sup Leaf x Leaf"
      by(case_tac x, simp_all add: is_sup_def leq_domainName_def)
    lemma DH_supLeSimp: "is_sup Leaf y (DH_sup Leaf y)"
      by(case_tac y, simp_all add: is_sup_def leq_domainName_def)
    lemma DH_sup_in_sup: "is_sup x y (DH_sup x y)"
      apply(induction x arbitrary: y)
       apply (simp_all add: DH_sup_Un DH_supUn DH_sup_Le DH_supLe DH_supLeSimp)
      apply(rename_tac xs x y)
      apply(case_tac y)
       apply (simp_all add: DH_sup_Un DH_supUn DH_sup_Le DH_supLe DH_supLeSimp)
      apply(rename_tac y2 y2s)
      apply(rule conjI)
      apply(clarify)
      apply(subgoal_tac "is_sup x y2s (DH_sup x y2s)")
       apply(simp add:is_sup_prepend_domain)
       apply force
      unfolding is_sup_def
      unfolding leq_domainName_def
      apply(clarify)
      apply(simp add: Leaf_Top)
      apply(clarify)
      apply(subgoal_tac "z = Leaf")
       apply(simp)
      apply(insert uncomparable_sup_is_Top)[1]
       apply metis
      done
     
    text {* domainName is a Lattice:*}
    instantiation domainName :: lattice
      begin
        print_context
      instance
        apply intro_classes
        apply(rule_tac x="DH_inf x y" in exI)
         apply(rule DH_inf_in_inf)
        apply(rule_tac x="DH_sup x y" in exI)
         apply(rule DH_sup_in_sup)
      done
    end
    


text{* Some helpfull lemmata:*}

lemma Unassigned_bot_step: "otherbot \<noteq> Unassigned \<Longrightarrow> (\<exists>x. x -- Unassigned \<le> otherbot)"
proof(induction otherbot)
  fix list otherbot
  assume "otherbot \<noteq> Unassigned \<Longrightarrow> \<exists>x. x -- Unassigned \<le> otherbot"
  show "list -- otherbot \<noteq> Unassigned \<Longrightarrow> \<exists>x. x -- Unassigned \<le> list -- otherbot"
    apply(case_tac "otherbot = Unassigned")
    apply simp_all
    by(simp add:Unassigned_bot)
qed(simp_all)

end
