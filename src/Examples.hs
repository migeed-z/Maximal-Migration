{-# Language QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}


module Examples where


import Lang
import Constraint
import Algorithms
import SolveEq
import Data.Either
import NPHard
import Formula


main3 :: IO ()    
main3 = return () 

--term
x_4 = (App (Vv "x") (Vi 4))
x_true = (App (Vv "x") (Vb True))
my_succ = (App (Vv "succ") x_true)
my_succ2 = (App (Vv "succ") x_4)
lam_z = (Lam Tdyn "z" (Vb True))
first_app = (App lam_z my_succ)
lam_y = (Lam Tdyn "y" first_app)
appx  = (App lam_y my_succ2)
final = (Lam Tdyn "x" appx)

--maximal
max_x_true = (App (Vv "x") (Vb True))
max_my_succ = (App (Vv "succ") x_true)
max_my_succ2 = (App (Vv "succ") x_4)
max_lam_z = (Lam Tint "z" (Vb True))
max_first_app = (App max_lam_z max_my_succ)
max_lam_y = (Lam Tint "y" max_first_app)
max_appx  = (App max_lam_y max_my_succ2)
max_final = (Lam (Tdyn ~> Tint) "x" max_appx)



--term 2
my_add = (App (App (Vv "+") x_4) x_true)
my_lam = (Lam (Tdyn) "x" my_add)
my_lam_max = (Lam (Tdyn ~> Tint) "x" my_add)


--term 3 (infinite lattice with a maximal migration)
app_y = (Lam Tdyn "y" (Vv "x"))
app_x = (App app_y (Vv "x"))
app_xx = (App app_x (Vv "x"))
lam = (Lam Tdyn "x" app_xx)


app_y_max = (Lam Tint "y" (Vv "x"))
app_x_max = (App app_y_max (Vv "x"))
app_xx_max = (App app_x_max (Vv "x"))
lam_max = (Lam Tdyn "x" app_xx_max)


    --a single function application
simple_app = (App (Lam Tdyn "x" (Vv "x")) (Vi 4))
simple_app_max = (App (Lam Tint "x" (Vv "x")) (Vi 4))


    --term with many applications
app_yxx = (App (Vv "succ") (App (App (Vv "y") (Vv "x")) (Vv "x")))
lam_xy = (Lam Tdyn "x" (Lam Tdyn "y" app_yxx))



    --term with no maximal migration
self_application = (Lam Tdyn "x" (App (Vv "x") (Vv "x")))

app_yxx2 = (App (Vv "succ") (App  (Vv "y") (App (Vv "x") (Vv "x"))))
lam_xy2 = (Lam Tdyn "x" (Lam Tdyn "y" app_yxx2))



app_xx_plus_xx = (App (Vv "x") (Vv "x"))
lam_xx_plus_xx = (Lam Tdyn "x" (App (App (Vv "+") app_xx_plus_xx) 
                                                          app_xx_plus_xx))

--ex1
succ_lam_true =  (Lam Tdyn "x" (App (Vv "x") 
                 (App (Vv "succ") (App (Vv "x") (Vb True)))))


succ_lam_true_max = (Lam (Tdyn ~> Tint) "x" (App (Vv "x") 
                 (App (Vv "succ") (App (Vv "x") (Vb True)))))

lam_succ_cnst =(compose_upto_match succ_lam_true tenv)
const_eq_lam_0 = lam_succ_cnst !! 0
lam_succ_unify0 =  (pleaseUnify const_eq_lam_0)

const_eq_lam_5 = lam_succ_cnst !! 5
lam_succ_unify5 =  (pleaseUnify const_eq_lam_5)


--ex2
lam_xx = (Lam Tdyn "x" (App (Vv "x") (Vv "x")))
lam_xx_cnst = (compose_upto_match lam_xx tenv)
const_eq_lam_xx_0 = lam_xx_cnst !! 0
lam_xx_unify0 = (pleaseUnify const_eq_lam_xx_0)
 
--ex3
app_xy_succ_true = (App (Vv "succ") 
                    (App (Lam Tdyn "y" (Vv "y")) 
                      (App (Lam Tdyn "x" (Vv "x")) (Vb True))))  

app_xy_succ_true_cnst =(compose_upto_match app_xy_succ_true tenv)
app_xy_succ_true_cnst_0 = app_xy_succ_true_cnst !! 0
app_xy_succ_true_cnst_unify0 = (pleaseUnify app_xy_succ_true_cnst_0)



--new term 1



lam_term_1 = (App (Lam Tdyn "x" (Lam Tdyn "y" (App (App (Vv "y") 
             (App (Vv "x") l)) (App (Vv "x") k)))) delta)

l = (Lam Tdyn "a" (Vv "a"))
k = (Lam Tdyn "b" (Lam Tdyn "c" (Vv "b")))
delta = (Lam Tdyn "d" (App (Vv "d") (Vv "d")))


--new term 2
app_term_2 = (App y (Lam Tdyn "e" (Lam Tdyn "m" (App (App (App (Vv "m") ident)
                          appmn)
                          appm))))
  


appm = (Lam Tdyn "m" (Lam Tdyn "v" (App (Vv "e") (App (Vv "m") (Vv "v")))))
appmn = (Lam Tdyn "m" (Lam Tdyn "n" (App (App (Vv "e") (Vv "m")) (App (Vv "e") (Vv "n")))))
ident = (Lam Tdyn "x" (Vv "x"))
y = Lam Tdyn "x" (App lam_h_xx lam_h_xx)
lam_h_xx = Lam Tdyn "h" (App (Vv "h") (App (Vv "x") (Vv "x")))



evil2 = (Lam  Tdyn "y" (Vv "x"))
evil1 = (App evil2 (Vv "x"))
evil0 = (App evil1 (Vv "x"))
evil = (Lam Tdyn "x" evil0)

evil2_m = (Lam  Tint "y" (Vv "x"))
evil1_m = (App evil2_m (Vv "x"))
evil0_m = (App evil1_m (Vv "x"))
evil_m = (Lam Tdyn "x" evil0_m)

evil_constraints = (constraint evil tenv)
evil_simPrec = (simPrec evil_constraints)
evil_simMatch = (simMatch (snd evil_simPrec))

-- c1 = (Cl (Pos "x0") (Neg "x1") (Pos "x2"))


succ_lam = (Lam Tdyn "x" (App (Vv "succ") (Vv "x")))

succ_app = (App (Vv "succ") (App (Lam Tdyn "y" (Vv "y")) 
           (App (Lam Tdyn "x" (Vv "x")) (Vb True)) ) )

lam_xyy = 
    Lam Tdyn "x" (Lam Tdyn "y" app_yxx)
    where
        app_yxx = (App (App (Vv "y") (Vv "x")) (Vv "x"))

lam_xyy_max =
    Lam Tdyn "x" (Lam (Tint ~> Tbool ~> Tint) "y" app_yxx)
    where
        app_yxx = (App (App (Vv "y") (Vv "x")) (Vv "x"))


lam_xyy_max2 =
    Lam Tint "x" (Lam (Tint ~> Tint~> Tint) "y" app_yxx)
    where
        app_yxx = (App (App (Vv "y") (Vv "x")) (Vv "x"))

evil_example = 
    (Lam Tdyn "x"
        (App ((Lam (Tdyn) "f" 
                    (App (App const (Vv "f"))
                        (App (Vv "f") (Vv "x")))))
            (Lam Tdyn "z" (Vi 1))
        ))


    where 
        const = (Lam Tdyn "x" (Lam Tdyn "y" (Vv "x")))   


evil_example_max = 
    (Lam Tint "x"
        (App ((Lam (Tdyn) "f" 
                    (App (App const (Vv "f"))
                        (App (Vv "f") (Vv "x")))))
            (Lam Tint "z" (Vi 1))
        ))

    where 
        const = (Lam Tint "x" (Lam Tint "y" (Vv "x")))   


lam_true = (Lam Tdyn "x" (App (Vv "x") my_succ))




--mapping

--sat
cp1 = Cl (Pos "x0") (Neg "x1") (Pos "x2")
cp2 = Cl (Neg "x0") (Pos "x1") (Pos "x2")
fpaper = [cp1,cp2]

--SAT
f1 = [Cl (Neg "x0") (Neg "x1") (Neg "x2")]

--unsat ( x1 || !x3) && (!x1 or x2 or x3) 
ca = Cl (Pos "x0") (Pos "x0") (Neg "x2")
cb = Cl (Neg "x0") (Pos "x1") (Pos "x2")
f2 = [ca, cb]


--SAT
cz1 = Cl (Pos "x0") (Neg "x1") (Pos "x0")
cz2 = Cl (Neg "x0") (Pos "x1") (Pos "x2")
cz3 = Cl (Neg "x0") (Neg "x0") (Neg "x0")
f3 = [cz1, cz2, cz3]


--unsat2
-- (x1 or x2) and
--   (x1 or bar{x2}) and
--   (bar{x1} or x2) and
--   (bar{x1} or bar{x2})

cx1 = Cl (Pos "x0") (Pos "x1") (Pos "x1")
cx2 = Cl (Pos "x0") (Neg "x1") (Pos "x0")
cx3 = Cl (Neg "x0") (Pos "x1") (Pos "x1")
cx4 = Cl (Neg "x0") (Neg "x1") (Neg "x0")
f4 = [cx1, cx2, cx3, cx4]


--(¬x2 ∨ x1) ∧ (¬x1 ∨ ¬x2 ∨ ¬x3) ∧
--(x1 ∨ x2) ∧ (¬x4 ∨ x3) ∧ (¬x5 ∨ x3) - SAT
cf51 = Cl (Neg "x0") (Pos "x1") (Pos "x1")
cf52 = Cl (Neg "x0") (Neg "x1") (Neg "x2")
cf53 = Cl (Pos "x0") (Pos "x1") (Pos "x1")
cf54 = Cl (Neg "x3") (Pos "x2") (Pos "x2")
cf55 = Cl (Neg "x4") (Pos "x2") (Pos "x2")
f5 = [cf51, cf52, cf53, cf54, cf55]


--(𝑥∨𝑦∨𝑧)∧(𝑥∨𝑦∨¬𝑧)∧(𝑥∨¬𝑦∨𝑧)∧(𝑥∨¬𝑦∨¬𝑧)∧(¬𝑥∨𝑦∨𝑧)∧(¬𝑥∨𝑦∨¬𝑧)
cf61 = Cl (Pos "x0") (Pos "x1") (Pos "x2")
cf62 = Cl (Pos "x0") (Pos "x1") (Neg "x2")
cf63 = Cl (Pos "x0") (Neg "x1") (Pos "x2")
cf64 = Cl (Pos "x0") (Neg "x1") (Neg "x2")
cf65 = Cl (Neg "x0") (Pos "x1") (Pos "x2")
cf66 = Cl (Neg "x0") (Pos "x1") (Neg "x2")

f6 = [cf61, cf62, cf63, cf64,cf65, cf66]

--7 clauses
cf71 = Cl (Pos "x0") (Pos "x1") (Pos "x2")
cf72 = Cl (Pos "x0") (Pos "x1") (Neg "x2")
cf73 = Cl (Pos "x0") (Neg "x1") (Pos "x2")
cf74 = Cl (Pos "x0") (Neg "x1") (Neg "x2")
cf75 = Cl (Neg "x0") (Pos "x1") (Pos "x2")
cf76 = Cl (Neg "x0") (Pos "x1") (Neg "x2")
cf77 = Cl (Neg "x0") (Neg "x1") (Pos "x2")

f7 = [cf71, cf72, cf73, cf74, cf75, cf76, cf77]


--unsat 
cy1 = Cl (Pos "x0") (Pos "x1") (Pos "x2")
cy2 = Cl (Pos "x0") (Pos "x1") (Neg "x2")
cy3 = Cl (Pos "x0") (Neg "x1") (Pos "x2")
cy4 = Cl (Pos "x0") (Neg "x1") (Neg "x2")
cy5 = Cl (Neg "x0") (Pos "x1") (Pos "x2")
cy6 = Cl (Neg "x0") (Pos "x1") (Neg "x2")
cy7 = Cl (Neg "x0") (Neg "x1") (Pos "x2")
cy8 = Cl (Neg "x0") (Neg "x1") (Neg "x2")

f8 = [cy1, cy2, cy3, cy4, cy5, cy6, cy7, cy8]
















