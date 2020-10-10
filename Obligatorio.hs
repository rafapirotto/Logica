module VerificdorTableaux where 
--{Diego Lauz : 201024}
--{Rafael Pirotto : 199390}

data Form = A Simbolo [Term] | Neg Form | Bc BinCon Form Form | All Var Form | Ex Var Form 
		deriving (Eq, Show)
data Term = V Var | C Simbolo | F Simbolo [Term]
		deriving (Eq, Show)
type Var = String
type Simbolo = String

data BinCon = And | Or | Impl
		deriving (Eq, Show)

type Rama = [Form]

type ArbolTableaux = [Rama]

data Regla = Conj | Disy | Exis Simbolo | Univer Simbolo

type Demostracion = [(Regla, Int)]

esDemostracionValida::ArbolTableaux -> Demostracion -> Bool
esDemostracionValida a d = case efecturaDemostracion a d of {
	([],[]) -> True;
	_ -> False
}

efecturaDemostracion::ArbolTableaux -> Demostracion -> (ArbolTableaux, Demostracion)
efecturaDemostracion = \a lst -> case lst of{
	[] -> (a, []);
	(x:xs) -> case verificarContradiccion (aplicarRegla (head a) x) of {
		[] -> efecturaDemostracion (tail a) xs ;
	l -> efecturaDemostracion ((l) ++ (tail a)) xs
	}
}

aplicarRegla::Rama -> (Regla, Int) -> ArbolTableaux
aplicarRegla = \fs reg -> case reg of {
	(Conj, i) -> [(take i fs) ++ (appConjuntiva (fs !! i)) ++ (drop (i+1) fs)];
	(Disy, i) -> case appDisyuntiva (fs !! i) of {
				(disIzq, disDer) -> [((take i fs) ++ [disIzq] ++ (drop (i+1) fs)), ((take i fs) ++ [disDer] ++ (drop (i+1) fs))]
	};
	(Exis n, i) -> case esNuevaConst n fs of {
				True -> [(take i fs) ++ [appExist n (fs !! i)] ++ (drop (i+1) fs)];
				False -> error "Mal aplicada la regla existencial, no se puede instanciar en una constante que no sea nueva."
		};
	(Univer n, i) -> case appUniversal n (fs !! i) of {
		(instancia, universal) -> [(take i fs) ++ [instancia] ++ (drop (i+1) fs) ++ [universal]]
	}
}

verificarContradiccion::ArbolTableaux -> ArbolTableaux
verificarContradiccion ls = filter (\m -> not (hayContradiccion m)) ls

--Ejercicio 3:

appConjuntiva ::Form  -> [Form]
appConjuntiva = \f -> case f of {
	Neg (Neg a) -> [a];
	Bc And a b -> [a,b];
	Neg (Bc Or a b) -> [Neg a, Neg b];
	Neg (Bc Impl a b) -> [a,Neg b];
	_ -> error "No se puede aplicar la regla conjuntiva";
}

appDisyuntiva :: Form  -> (Form, Form)
appDisyuntiva = \f -> case f of {
	Bc Or a b -> (a,b);
	Neg (Bc And a b) -> (Neg a,Neg b);
	Bc Impl a b -> (Neg a,b);
	_ -> error "No se puede aplicar la regla disyuntiva";
}

appExist::Simbolo -> Form -> Form 
appExist = \vf f -> case f of {
	Ex vi g -> sustituir g vi vf;
	Neg (All vi g) -> sustituir (Neg g) vi vf;
	_ -> error "No se puede aplicar la regla existencial";
}

appUniversal::Simbolo -> Form -> (Form, Form)
appUniversal = \vf f -> case f of {
	All vi g -> ((sustituir g vi vf),(All vi g));
	Neg (Ex vi g) -> ((Neg (sustituir g vi vf)),(Neg (Ex vi g)));
	_ -> error "No se puede aplicar la regla universal";
}

esNuevaConst:: Simbolo -> Rama -> Bool
esNuevaConst = \s r -> case r of {
	[] -> True;
	[x] -> x==s;--lo agregue yo
	x:xs -> (esNuevaConstAux s x) && (esNuevaConst s xs);
}

hayContradiccion::Rama -> Bool
hayContradiccion = \r -> case r of {
	[] -> False;
	x:xs -> (hayIguales x xs) || hayContradiccion xs;--para mi es con el negado
}

--Funciones Auxiliares

hayIguales:: Form -> [Form] -> Bool
hayIguales = \x lst -> case lst of {
	[] -> False;
	[s] -> Neg(s)==x;--lo agregue yo
	y:ys -> igualesForm x y || hayIguales x ys;
}

igualesForm:: Form -> Form -> Bool
igualesForm = \x y -> case x of {
	A n l -> case y of {
		A m k -> igualesListaTerm l k && n==m;
		_ -> False;
	};
	Neg a -> case y of {
		Neg c -> igualesForm a c;
		_ -> False;
	};
	Bc And a b -> case y of {
		Bc And c d -> igualesForm a c && igualesForm b d;
		_ -> False;
	};
	Bc Or a b -> case y of {
		Bc Or c d -> igualesForm a c && igualesForm b d;
		_ -> False;
	};
	Bc Impl a b -> case y of {
		Bc Impl c d -> igualesForm a c && igualesForm b d;
		_ -> False;
	};
	All n a -> case y of {
		All m c -> igualesForm a c && n==m;
		_ -> False;
	};
	Ex n a -> case y of {
		Ex m c -> igualesForm a c && n==m;
		_ -> False;
	};
}

igualesTerm:: Term -> Term -> Bool
igualesTerm = \x y -> case x of {
	V a -> case y of {
		V b -> a==b;--ver si es con el negado
		_ -> False;
	};
	C a -> case y of {
		C b -> a==b;
		_ -> False;
	};
	F n l -> case y of {
		F m k -> m==n && igualesListaTerm l k;
		_ -> False;
	};
}

igualesListaTerm:: [Term] -> [Term] -> Bool
igualesListaTerm = \l k -> case l of {
	[] -> case k of {
		[] -> True;
		_ -> False;
	};
	x:xs -> case k of {
		[] -> False;
		y:ys -> igualesTerm x y && igualesListaTerm xs ys;
	};
}

esNuevaConstAux::Simbolo -> Form -> Bool
esNuevaConstAux = \s f -> case f of {
	A n t -> esNuevaConstTerm s t;
	Neg a -> esNuevaConstAux s a;
	Bc And a b -> (esNuevaConstAux s a) && (esNuevaConstAux s b);
	Bc Or a b -> (esNuevaConstAux s a) && (esNuevaConstAux s b);
	Bc Impl a b -> (esNuevaConstAux s a) && (esNuevaConstAux s b);
	All p a -> esNuevaConstAux s a;
	Ex p a -> esNuevaConstAux s a;
}

esNuevaConstTerm::Simbolo -> [Term] -> Bool
esNuevaConstTerm = \s t -> case t of {
	[] -> True;
	x:xs -> case x of {
		V v -> True;
		C c -> s==c;
		F n l -> (esNuevaConstTerm s l) && (esNuevaConstTerm s xs);
	}
}

sustituir::Form -> Simbolo -> Var -> Form
sustituir = \f vi vf -> case f of {
	A nom lst -> A nom (sustituirAux lst vi vf);
	Neg a -> Neg (sustituir a vi vf);
	Bc And a b -> Bc And (sustituir a vi vf) (sustituir b vi vf);
	Bc Or a b -> Bc Or (sustituir a vi vf) (sustituir b vi vf);
	Bc Impl a b -> Bc Impl (sustituir a vi vf) (sustituir b vi vf);
	All p a -> All p (sustituir a vi vf);
	Ex p a -> Ex p (sustituir a vi vf);
}

sustituirAux::[Term] -> Simbolo -> Var -> [Term]
sustituirAux = \t vi vf -> case t of {
	[] -> [];
	x:xs -> case x of {
		V v -> case v==vi of {
			True -> [V vf] ++ sustituirAux xs vi vf;
			False -> [V v] ++ sustituirAux xs vi vf;
		};
		C g -> [C g] ++ sustituirAux xs vi vf;
		F n l -> (sustituirAux l vi vf) ++ sustituirAux xs vi vf;
	}
}


--Ejercicio 5:

--a)
arbol_a::ArbolTableaux
arbol_a = undefined

demostracion_a::Demostracion
demostracion_a = undefined

--b)
arbol_b::ArbolTableaux
arbol_b = undefined

demostracion_b::Demostracion
demostracion_b = undefined

--c)
arbol_c::ArbolTableaux
arbol_c = undefined

demostracion_c::Demostracion
demostracion_c = undefined

--d)
arbol_d::ArbolTableaux
arbol_d = undefined

demostracion_d::Demostracion
demostracion_d = undefined

--e)
arbol_e::ArbolTableaux
arbol_e = undefined

demostracion_e::Demostracion
demostracion_e = undefined

--f)
arbol_f::ArbolTableaux
arbol_f = undefined

demostracion_f::Demostracion
demostracion_f = undefined

--g)
arbol_g::ArbolTableaux
arbol_g = undefined

demostracion_g::Demostracion
demostracion_g = undefined