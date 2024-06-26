theory ex1
imports Main
begin

text \<open>
  Natural Number And list:  https://www.youtube.com/watch?v=VDwdFPrum0E
\<close>

text \<open> 1. Calulating with natural number\<close>
value "(2::nat) + 2" text \<open> type infer, addition\<close>
value "(2::nat) * (5+3)"  text \<open> multiply & () \<close>
value "(2::nat) * 6 - 7* (5+3)" text \<open> nat is >= 0\<close>


text \<open>
   2. Natural Number laws: 
   commutativity and assosiativity for addition of natural number
\<close>

lemma "(x::nat) + y = y + x"
  apply auto
  done

lemma "((x::nat) + y) + z = x + (y + z)"
  apply auto
  done

text \<open>3. Counting elements of a list, using a recurrsive definition\<close>
fun count :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "count [] _ = 0" |
  "count (x # xs) y = (
    if x = y 
      then Suc(count xs y) 
    else 
      count xs y
  )"

text \<open>explain of above by chatgpt:
  This Isabelle/HOL function definition is named count, and it takes two arguments:
  'a list: This represents a list of elements of some type 'a.
  'a: This represents an element of the same type as the elements in the list.
  
  The return type of this function is nat, which means it returns a natural number.
  
  The purpose of this function is to count the number of occurrences 
  of a specific element in a list. 
  For example, if you have a list [1, 2, 3, 1, 4, 1] and you call count [1, 2, 3, 1, 4, 1] 1, 
  it should return 3 because 1 appears three times in the list.

  count [] _ = 0 
  is a pattern matching rule in the function definition of count. 
  It handles the case where the input list is empty, 
  and it ignores the second argument (the element to count) 
  because an empty list cannot contain any elements.

  count (x # xs) y: 
  This pattern matches a non-empty list, 
  where x is the head of the list, and xs is the tail of the list. 
  The # symbol is the list constructor, separating the head x from the tail xs.
  y: This is the element that you want to count in the list.

  The next line is structured as an if-else statement:
  if x = y then Suc (count xs y): 
  If the head of the list x is equal to the element y, 
  then increment the count by 1 using Suc and recursively call count on the tail of the list xs 
  with the same element y. 
  This part of the line handles the case where the head of the list matches the element 
  you are counting.
  
  else count xs y: 
  If the head of the list x is not equal to the element y, 
  then recursively call count on the tail of the list xs with the same element y. 
  This part of the line handles the case where the head of the list does not match 
  the element you are counting.
\<close>

value "count [0,1,2,0] (0::nat)"

text \<open>auto proof\<close>
theorem "count xs x \<le> length xs"
  by(induct xs) auto

text \<open>proof by induct using simp\<close>
theorem "count xs x \<le> length xs"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs')
  assume IH: "count xs' x \<le> length xs'"
  show "count (a # xs') x \<le> length (a # xs')"
  proof (cases "a = x")
    case True
    with IH show ?thesis by simp
  next
    case False
    with IH show ?thesis by simp
  qed
qed


text \<open>replace simp with more detail\<close>
theorem "count xs x \<le> length xs"
proof (induct xs)
  case Nil
  have A:"count [] x = 0" by simp (*(metis count.simps(1))*)
  have B:"length [] = 0" by simp
  with A have C:"count [] x = length []" by simp
  from C have D: "count [] x \<le> length []" by simp
  from D show ?case .
next
  case (Cons a xs') 
  then have A:"count xs' x \<le> length xs'" by simp
  have B:"length (a # xs') = Suc (length xs')" by simp
  then show C:"count (a # xs') x \<le> length (a # xs')"
  proof (cases "a = x")
    case True
    then have a:"count (a # xs') x = Suc (count xs' x)" by simp
    with A and B have "count (a # xs') x \<le> length (a # xs')" by simp
    then show ?thesis .
  next
    case False
    then have a: "count (a # xs') x = count xs' x" by simp
    with A and B have "count (a # xs') x \<le> length (a # xs')" by simp
    then show ?thesis .
  qed
qed


text \<open>replace all simp by exact rule\<close>
theorem "count xs x \<le> length xs"
proof (induct xs)
  case Nil
  have A:"count [] x = 0" by (metis count.simps(1)) (*by count definition case 1*)
  have B:"length [] = 0" by (metis list.size(3)) (*by list.size definition*)
  with A have C:"count [] x = length []" by (rule trans_sym)
  from C have D: "count [] x \<le> length []" by (rule eq_refl)
  from D show ?case .
next
  case (Cons a xs') 
  then have A:"count xs' x \<le> length xs'" by (metis)
  have B:"length (a # xs') = Suc (length xs')" by (rule length_Cons)
  then show C:"count (a # xs') x \<le> length (a # xs')"
  proof (cases "a = x")
    case True
    then have a:"count (a # xs') x = Suc (count xs' x)" by (metis count.simps(2))
    with A and B have "count (a # xs') x \<le> length (a # xs')" by simp (*todo*)
    then show ?thesis .
  next
    case False
    then have a: "count (a # xs') x = count xs' x" by (metis count.simps(2))
    with A and B have "count (a # xs') x \<le> length (a # xs')" by simp (*todo*)
    then show ?thesis .
  qed
qed
