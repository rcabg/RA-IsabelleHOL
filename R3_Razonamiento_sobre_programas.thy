chapter {* R3: Razonamiento sobre programas *}
 
theory R3_Razonamiento_sobre_programas
imports Main 
begin
 
text {* --------------------------------------------------------------- 
  Ejercicio 1.1. Definir la función
     sumaImpares :: nat \<Rightarrow> nat
  tal que (sumaImpares n) es la suma de los n primeros números
  impares. Por ejemplo,
     sumaImpares 5  =  25
  ------------------------------------------------------------------ *}
 
fun sumaImpares :: "nat \<Rightarrow> nat" where
  "sumaImpares 0 = 0"
| "sumaImpares (Suc n) = sumaImpares n + (2*n+1)"
 
text {* --------------------------------------------------------------- 
  Ejercicio 1.2. Escribir la demostración detallada de 
     sumaImpares n = n*n
  ------------------------------------------------------------------- *}
 
-- "La demostración detallada es"

lemma "sumaImpares n = n*n"
proof (induct n)
  show "sumaImpares 0 = 0*0" by simp
next
  fix n
  assume HI: "sumaImpares n=n*n"
  have "sumaImpares (Suc n) =sumaImpares n + (2*n+1)" by simp
  also have "... = n*n + (2*n+1)" using HI by simp
  finally show "sumaImpares (Suc n) =(Suc n) *(Suc n)" by simp
qed
 
text {* --------------------------------------------------------------- 
  Ejercicio 2.1. Definir la función
     sumaPotenciasDeDosMasUno :: nat \<Rightarrow> nat
  tal que 
     (sumaPotenciasDeDosMasUno n) = 1 + 2^0 + 2^1 + 2^2 + ... + 2^n. 
  Por ejemplo, 
     sumaPotenciasDeDosMasUno 3  =  16
  ------------------------------------------------------------------ *}
 
fun sumaPotenciasDeDosMasUno :: "nat \<Rightarrow> nat" where
  "sumaPotenciasDeDosMasUno 0 = 2"
| "sumaPotenciasDeDosMasUno (Suc n) = 
      sumaPotenciasDeDosMasUno n + 2^(n+1)"
 
text {* --------------------------------------------------------------- 
  Ejercicio 2.2. Escribir la demostración detallada de 
     sumaPotenciasDeDosMasUno n = 2^(n+1)
  ------------------------------------------------------------------- *}
 
lemma "sumaPotenciasDeDosMasUno n = 2^(n+1)"
proof (induct n)
  show "sumaPotenciasDeDosMasUno 0 = 2^(0+1)" by simp
next
  fix n
  assume HI: "sumaPotenciasDeDosMasUno n = 2^(n+1)"
  have "sumaPotenciasDeDosMasUno (Suc n) = sumaPotenciasDeDosMasUno n + 2^(n+1)" by simp
  also have "... = 2^(n+1) + 2^(n+1)" using HI by simp
  also have "... = 2^((Suc n) + 1)" by simp
  finally show "sumaPotenciasDeDosMasUno (Suc n) = 2 ^ (Suc n + 1)" by simp
qed
 
text {* --------------------------------------------------------------- 
  Ejercicio 3.1. Definir la función
     copia :: nat \<Rightarrow> 'a \<Rightarrow> 'a list
  tal que (copia n x) es la lista formado por n copias del elemento
  x. Por ejemplo, 
     copia 3 x = [x,x,x]
  ------------------------------------------------------------------ *}
 
fun copia :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "copia 0 x       = []"
| "copia (Suc n) x = x # copia n x"
 
text {* --------------------------------------------------------------- 
  Ejercicio 3.2. Definir la función
     todos :: ('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool
  tal que (todos p xs) se verifica si todos los elementos de xs cumplen
  la propiedad p. Por ejemplo,
     todos (\<lambda>x. x>(1::nat)) [2,6,4] = True
     todos (\<lambda>x. x>(2::nat)) [2,6,4] = False
  ------------------------------------------------------------------ *}
 
fun todos :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
  "todos p []     = True"
| "todos p (x#xs) = (p x \<and> todos p xs)"
 
text {* --------------------------------------------------------------- 
  Ejercicio 3.2. Demostrar detalladamente que todos los elementos de
  (copia n x) son iguales a x. 
  ------------------------------------------------------------------- *}
 
lemma "todos (\<lambda>y. y=x) (copia n x)"
proof (induct n)
  show "todos (\<lambda>y. y=x) (copia 0 x)" by simp
next
  fix n
  assume HI: "todos (\<lambda>y. y=x) (copia n x)"
  have "todos (\<lambda>y. y=x) (copia (Suc n) x) = todos (\<lambda>y. y=x) (x#(copia n x))" by simp
  also have "... = todos (\<lambda>y. y=x) (copia n x)" by simp
  finally show "todos (\<lambda>y. y=x) (copia (Suc n) x)" using HI by simp
qed

text {* --------------------------------------------------------------- 
  Ejercicio 4.1. Definir la función
    factR :: nat \<Rightarrow> nat
  tal que (factR n) es el factorial de n. Por ejemplo,
    factR 4 = 24
  ------------------------------------------------------------------ *}
 
fun factR :: "nat \<Rightarrow> nat" where
  "factR 0       = 1"
| "factR (Suc n) = Suc n * factR n"
 
text {* --------------------------------------------------------------- 
  Ejercicio 4.2. Se considera la siguiente definición iterativa de la
  función factorial 
     factI :: "nat \<Rightarrow> nat" where
     factI n = factI' n 1
 
     factI' :: nat \<Rightarrow> nat \<Rightarrow> nat" where
     factI' 0       x = x
     factI' (Suc n) x = factI' n (Suc n)*x
  Demostrar que, para todo n y todo x, se tiene 
     factI' n x = x * factR n
  Indicación: La propiedad mult_Suc es 
     (Suc m) * n = n + m * n
  Puede que se necesite desactivarla en un paso con 
     (simp del: mult_Suc)
  ------------------------------------------------------------------- *}
 
fun factI' :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "factI' 0       x = x"
| "factI' (Suc n) x = factI' n (x * Suc n)"
 
fun factI :: "nat \<Rightarrow> nat" where
  "factI n = factI' n 1"
 
lemma fact: "factI' n x = x * factR n"
proof (induct n arbitrary: x)
  show "\<And>x. factI' 0 x = x * factR 0" by simp
next 
  fix n
  assume HI: "\<And>x. factI' n x = x * factR n"
  show "\<And>x. factI' (Suc n) x = x * factR (Suc n)"
  proof -
    fix x
    have "factI' (Suc n) x = factI' n (x * Suc n)"   by simp
    also have "... = (x * Suc n) * factR n" using HI by simp
    also have "... = x * (Suc n * factR n)" by (simp del: mult_Suc)
    also have "... = x * factR (Suc n)" by simp
    finally show "factI' (Suc n) x = x * factR (Suc n)" by simp
  qed
qed
 
text {* --------------------------------------------------------------- 
  Ejercicio 4.3. Escribir la demostración detallada de
     factI n = factR n
  ------------------------------------------------------------------- *}
 
corollary "factI n = factR n"
proof -
  fix n
  have "factI n = factI' n 1" by simp
  also have "... = 1 * factR n" by (simp add:fact)
  finally show "factI n = factR n" by simp
qed
 
text {* --------------------------------------------------------------- 
  Ejercicio 5.1. Definir, recursivamente y sin usar (@), la función
     amplia :: 'a list \<Rightarrow> 'a \<Rightarrow> 'a list
  tal que (amplia xs y) es la lista obtenida añadiendo el elemento y al
  final de la lista xs. Por ejemplo,
     amplia [d,a] t = [d,a,t]
  ------------------------------------------------------------------ *}
 
fun amplia :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "amplia []     y = [y]"
| "amplia (x#xs) y = x # amplia xs y"
 
text {* --------------------------------------------------------------- 
  Ejercicio 5.2. Escribir la demostración detallada de
     amplia xs y = xs @ [y]
  ------------------------------------------------------------------- *}
 
lemma "amplia xs y = xs @ [y]"
proof (induct xs)
  show "amplia [] y = [] @ [y]" by simp
next
  fix a xs
  assume HI: "amplia xs y = xs @ [y]"
  have "amplia (a#xs) y =a # amplia xs y" by simp
  also have "... = a # (xs @[y]) " using HI by simp
  also have "... =(a # xs) @[y] " using HI by simp
  finally show "amplia (a#xs) y= (a # xs) @[y]" by simp
qed
 
end