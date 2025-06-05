type ltl = 
  | Top
  | Bot 
  | Atom of string 
  | Not of ltl 
  | Or of ltl*ltl
  | And of ltl*ltl 
  | X of ltl 
  | G of ltl
  | F of ltl
  | U of ltl*ltl
  | R of ltl*ltl

type noeud = {name : string}


type state = {etat : string}

type kripke_struct = {
  q : state list; 
  init: state list; 
  transition : (state * state) list; 
  valuation : (state * (ltl list)) list ;
  (* une fonction qui à un état associe un ensemble de formules ltl*)
  (* Cf définition dans le diapo *)
} 

type buchi_automate = {
  q : state list; 
  init : state list; 
  final : state list; 
  transition : (state * state) list; 
  valuation : (state * (ltl list)) list
  (* La valuation correspond au "L" dans la définition du LGBA (pour labelled generalised buchi automaton) *)
}

(* Fin des declarations de types *)

(* On va maintenant coder un système d'ensemble avec des listes *)
(* Exactement les mêmes que pour le model checker ctl *)
let rec prive (a: 'a list ) (b: 'a list) : 'a list = 
  (* Réalise A\B *)
  match a with 
  | [] -> []
  | x::q -> if (List.mem x b) then prive q b 
  else x::(prive q b)

let rec union (a: 'a list) (b: 'a list) : 'a list = 
  (* Réalise A U B (sans doublons si a et b sont sans doublons)*)
  match a with 
  | [] -> b
  | x::q -> if (List.mem x b) then union q b 
  else x::(union q b)

let rec inter (a: 'a list) (b:'a list) : 'a list = 
  (* réalise a inter b *)
  match a with 
  | [] -> []
  | x::q -> if (List.mem x b) then x::(inter q b)
  else inter q b

let appartient (x: 'a) (a: 'a list) :bool = 
  List.mem x a 

let inclus (a: 'a list) (b: 'a list) : bool = 
  (* Test si A inclus dans B *)
  match (prive a b) with (* A\B est vide ssi A inclus dans B *)
  | [] -> true 
  | _ -> false

exception Elem_pas_present
(* Supprime x de a, et lève une exception si x n'est pas dans a*)
let rec suppr (x:'a) (a: 'a list) : 'a list = 
  match a with 
  | [] -> raise Elem_pas_present
  | y::q -> if (x=y) then q 
  else y::(suppr x q)



(* Fonction auxiliaire qui décide une égalité ensembliste entre a et b *)
let rec egal_ens_aux (a: 'a list) (b : 'a list) : bool = 
  match a with 
  | [] -> (b = [])
  | x::q -> egal_ens_aux q (suppr x b)

let egal_ens (a: 'a list) (b:'a list) : bool = 
  try 
    egal_ens_aux a b 
  with
  | Elem_pas_present -> false 

(* Fin de l'implémentation des ensembles *)

(* Pour le débug *)
let rec print_ltl (f: ltl) : unit = 
  match f with 
  | Top -> print_string"Top"
  | Bot -> print_string"Bot"
  | Atom p -> print_string p
  | Not g -> print_string "Not "; print_ltl g 
  | X g ->  print_string "X "; print_ltl g 
  | Or (f1,f2) -> print_ltl f1; print_string" || "; print_ltl f2
  | And (f1,f2) -> print_ltl f1; print_string" && "; print_ltl f2
  | G g -> print_string "G "; print_ltl g 
  | F g -> print_string "F "; print_ltl g 
  | U (f1,f2) -> print_ltl f1; print_string" U "; print_ltl f2
  | R (f1,f2) -> print_ltl f1; print_string" R "; print_ltl f2


let rec print_list = function 
  [] -> ()
  | e::l -> print_ltl e ; print_string " " ; print_list l
(* Fin des fonctions de debug *)



(* Renvoie une formule équivalente à f, ne contenant plus aucun F, G *)
let suppr_fg (phi : ltl) : ltl = 
  match phi with 
  | F psi -> U (Top, psi)
  | G psi -> R (Bot, psi)
  | _ -> phi

(* Cette fonction nous servira a transformé notre formule en 
automate de büchi généralisé, en effet, on doit d'abord transformer
notre formule f en forme normal négative *)


(* METTRE DANS LE DOC MATHCHA LES EXPLICATIONS DE FORME NORMAL
NEGATIVE *)

(* Transforme une formule f en une formule f' équivalente
mise sous forme normale négative *)
let rec fnn (psi:ltl) : ltl = 
  match psi with
  | Top | Bot | Atom _ -> psi 
  | Or (psi1, psi2) -> Or (fnn psi1, fnn psi2)
  | And (psi1, psi2) -> And (fnn psi1, fnn psi2)
  | U (psi1, psi2) -> U (fnn psi1, fnn psi2)
  | R (psi1, psi2) -> R (fnn psi1, fnn psi2)
  | X phi -> X (fnn phi)
  | F _ | G _ -> fnn (suppr_fg psi)
  | Not phi -> 
    (* On va ici appliqué les lois de De Morgan *)
    (* Et les lois de dualités spécifiques à la logique LTL *)
    begin 
      match phi with 
      | Top ->  Bot 
      | Bot -> Top
      | Atom _ -> Not phi
      | Not psi2 -> (fnn psi2) (* Elimination de la double négation*)
      | Or (psi1,psi2) -> And (fnn (Not psi1), fnn (Not psi2)) (* Loi de De Morgan *)
      | And (psi1,psi2) -> Or (fnn (Not psi1), fnn (Not psi2))
      | X psi2 -> X (fnn (Not psi2))
      | F _ | G _ -> fnn (Not (suppr_fg phi))
      | U (psi1, psi2) -> R (fnn (Not psi1), fnn (Not psi2))
      | R (psi1, psi2) -> U (fnn (Not psi1), fnn (Not psi2))
    end
  

(* On va maintenant coder les fonctions de wikipedia : https://en.wikipedia.org/wiki/Linear_temporal_logic_to_B%C3%BCchi_automaton *)
(* On a ici des formules ne contenant pas de F, de G, et dont toutes les négations précèdes les litteraux
(mis sous forme normale négative) *)
let curr1 (phi: ltl) : ltl list = 
  match phi with 
  | U (psi1, psi2) -> [psi1]
  | R (psi1, psi2) -> [psi2]
  | Or (psi1, psi2) -> [psi2]
  | _ -> []

let next1 (phi: ltl) : ltl list = 
  match phi with 
  | U (psi1, psi2) -> [phi]
  | R (psi1 ,psi2) -> [phi]
  | _ -> []

let curr2 (phi : ltl): ltl list = 
  match phi with 
  | U (psi1, psi2) -> [psi2]
  | R (psi1, psi2) -> [psi1; psi2]
  | Or (psi1, psi2) -> [psi1]
  | _ -> []

let neg (phi : ltl) : ltl = 
  match phi with 
  | Top -> Bot 
  | Bot -> Top
  | Atom p -> Not phi 
  | Not (Atom p) -> Atom p 
  | _ -> phi 

(* Récupère l'ensemble d'éléments associé à un noeud dans set  *)
let rec get_set (set : (noeud * ('a list)) list) (q:noeud) : 'a list = 
  match set with 
  | [] -> failwith "From get_set : Valeur non présente dans set"
  | (x,l)::p -> if (x.name = q.name) then l else get_set p q


(* Renvoie incoming_u en version modifiée de tels manière que Incoming_u(q) := Incoming_u(q) U incoming *)
let rec edit_incoming (incoming_u : ((noeud * (noeud list)) list)) (incoming : noeud list) (q:noeud): (noeud * (noeud list)) list = 
  match incoming_u with 
  | [] -> [q,incoming]
  | (x,l)::p -> if (x.name = q.name) then (q, union l incoming)::p
  else (x,l)::(edit_incoming p incoming q)


(* Renvoie true si il existe q ∈ nodeset / q.next=node.next et q.old=node.old et dans ce cas la : modifie 
q.incoming par q.incoming ∪ node.incoming
Sinon renvoie false*)
let rec exists (next_u : (noeud * (ltl list)) list ) (next : ltl list) (now_u : (noeud * (ltl list)) list) (old: ltl list) (incoming: noeud list) (incoming_u : ((noeud * (noeud list)) list) ref) (nodeset: noeud list) : bool= 
  match nodeset with 
  | [] -> false 
  | q::p -> let lnext = get_set next_u q in 
  let lnow = get_set now_u q in 
  if ((egal_ens lnext next) && (egal_ens lnow old)) then (
    let incoming_bis = edit_incoming (!incoming_u) incoming q in
    incoming_u := incoming_bis;
    let _ = exists next_u next now_u old incoming incoming_u p in true
  )
  else exists next_u next now_u old incoming incoming_u p

(* Renvoie le plus grand nombre présent dans nodeset *)
let rec max_name (l: noeud list) = 
  match l with 
  | [] -> 0
  | x::q -> max (int_of_string (x.name)) (max_name q)

(* Fonction expand de  https://en.wikipedia.org/wiki/Linear_temporal_logic_to_B%C3%BCchi_automaton *)
let expand (curr: ltl list) (old : ltl list) (next : ltl list) (incoming : noeud list)  = 
  let nodes_u = ref [] in
  let incoming_u = ref [] in
  let now_u = ref [] in
  let next_u = ref [] in
  let rec expand_aux (curr: ltl list) (old : ltl list) (next : ltl list) (incoming : noeud list) : unit = 
    if curr = [] then (
      if (exists (!next_u) next (!now_u) old incoming incoming_u (!nodes_u)) then ()
      else (
        let q = {
          name = string_of_int ((max_name (!nodes_u))+1)
        } in
        nodes_u := union (!nodes_u) [q];
        incoming_u := union (!incoming_u) [(q, incoming)];
        now_u := union (!now_u) [(q,old)];
        next_u := union (!next_u) [(q,next)];
        (expand_aux next [] [] [q])
      ) 
    )
    else ( 
      let f = List.hd curr in 
      let curr3 = List.tl curr in 
      let old3 = union old [f] in 
      match f with 
      | Top | Bot | Atom _ | Not (Atom _) -> 
        if ((f= Bot) || (appartient (neg f) old3)) then ()
        else (expand_aux curr3 old3 next incoming)
      | And (f1,f2) -> 
        (expand_aux (union curr3 (prive [f1;f2] old3)) old3 next incoming)
      | X g -> 
        (expand_aux curr3 old3 (union next [g]) incoming)
      | Or (f1,f2) | U (f1,f2) | R (f1,f2) -> 
        (expand_aux (union curr3 (prive (curr1 f) old3)) old3 (union next (next1 f)) incoming);
        (expand_aux (union curr3 (prive (curr2 f) old3)) old3 next incoming)
      | Not _ | G _ | F _ -> failwith "Formule non mise sous forme normale négative"
    )
    in (expand_aux curr old next incoming); (!nodes_u, !now_u, !incoming_u)
    
let create_graph (f :ltl) = 
  let init = {name = "init"} in 
  expand [f] [] [] [init] 
  

(* Transforme une structure de kripke en un automate de buchi, (tout les états sont finaux) 
On renomme ici les états par k_(nom de l'état) afin de pouvoir différencier les états provenants d'une structure
de kripke de ceux provenant d'un automate de buchi*)
let kripke_to_buchi (k: kripke_struct) : buchi_automate = 
  {q = List.map (fun x -> {etat = "k_" ^ x.etat}) (k.q); 
  init = List.map (fun x -> {etat = "k_" ^ x.etat}) (k.init); 
  transition = List.map (fun (x,y) -> ({etat = "k_" ^ x.etat}, {etat = "k_" ^ y.etat})) (k.transition); 
  final = List.map (fun x -> ({etat = "k_" ^ x.etat})) (k.q); 
  valuation = List.map (fun (x,f) -> ({etat = "k_" ^ x.etat}, f)) (k.valuation)}

(* Construit Δ = {(q,q')| q,q' ∈ Nodes and q ∈ Incoming(q') } *)
let rec build_transition (nodes: noeud list) (incoming: (noeud * (noeud list)) list) : (state*state) list  =
  (* Renvoie  {(node,q')| node,q' ∈ Nodes and node ∈ l }*)
  let rec build_transition_with_list (nodes :noeud list) (node : noeud) (l: noeud list) : (state*state) list =
    match l with 
    | [] -> []
    | q::p -> if (appartient q nodes) then ({etat = q.name},{etat = node.name})::(build_transition_with_list nodes node p)
    else (build_transition_with_list nodes node p)
  in
  match incoming with 
  | [] -> []
  | (q',l)::p -> if ((appartient q' nodes)) then (build_transition_with_list nodes q' l)@(build_transition nodes p)
  else (build_transition nodes p)

(* Construit Q0 = { q ∈ Nodes | init ∈ Incoming(q) } *)
let rec build_init (nodes : noeud list) (incoming: (noeud*(noeud list)) list) (init: noeud) : state list = 
  match incoming with 
  | [] -> []
  | (q,l)::p -> if ((appartient init l) && (q.name <> "init")) then ({etat = q.name})::(build_init nodes p init) 
  else (build_init nodes p init) (* on exclus ici init avec la condition q.name <> "init" car on veut les q∈ Nodes et init n'est pas 
  dans Nodes *)

(* Extrait  l'ensemble des formules de now (qui est de type (noeud*ltl))*)
let rec extract_ltl (now: (noeud*ltl) list) : ltl list = 
  match now with 
  | [] -> []
  | (q,f)::p -> let res = extract_ltl p in 
    if (appartient f res) then res
    else f::res

(* On va maintenant construire les états finaux *)


(* Construit Fg = { q ∈ Nodes | g2 ∈ Now(q) or g ∉ Now(q) } où g = g1 U g2*)
let rec build_fg (nodes: noeud list) (now: (noeud* (ltl list)) list) (g1:ltl) (g2: ltl) : state list = 
  match now with 
  | [] -> []
  | (q,l)::p -> let res = (build_fg nodes p g1 g2) in
    if ((appartient g2 l || not (appartient (U (g1,g2)) l)) && (not (appartient {etat = q.name} res))) 
      then ({etat = q.name}::res)
  else res

(* Détermine si g est une sous formule de f *)
let rec est_sous_formule (g: ltl) (f: ltl) : bool = 
  if (f=g) then true else 
  match f with 
  | Top | Bot | Atom _ -> (f=g) (*false donc*)
  | Not f' | X f' | F f' | G f' -> est_sous_formule g f'
  | Or (f1,f2) | And (f1,f2) | U (f1,f2) | R (f1,f2)  -> (est_sous_formule g f1) || (est_sous_formule g f2)

(* Extrait les sous formule de f de la forme phi U psi  *)
let rec extrait_sous_formule (f: ltl) : ltl list = 
  match f with 
  | Atom p -> [U (Atom p, Atom p);U( Not (Atom p), Not (Atom p))]
  | Top -> [U (Top, Top)]
  | Bot -> []
  | U (f1,f2) -> f::(union (extrait_sous_formule f1) (extrait_sous_formule f2))
  | And (f1,f2) | Or (f1,f2) -> (union (extrait_sous_formule f1) (extrait_sous_formule f2))
  | R (f1,f2) -> 
      (* R(f1,f2) équivaut à Not U (Not f1,Not f2) *)
      f::(union (extrait_sous_formule (Not f1)) (extrait_sous_formule (Not f2)))
  | X f1 | Not f1 -> extrait_sous_formule f1 
  | G _ | F _ -> failwith"formule non mise sous forme normale négative"

(* Transforme un ensemble de noeud en un ensemble d'états *)
let rec nodes_to_state (nodes : noeud list) : state list = 
  match nodes with 
  | [] -> []
  | x::q -> {etat = x.name}::(nodes_to_state q)

let build_final (f: ltl) (nodes: noeud list) (now : (noeud* (ltl list)) list) : state list = 
  let rec aux (set : ltl list) : state list list = 
  (* Construit F = { Fg | g ∈ cl( f ) } *)
  match set with 
  | [] -> []
  | U(g1,g2)::q -> (build_fg nodes now g1 g2)::(aux q)
  | R(g1,g2)::q -> (build_fg nodes now (Not g1) (Not g2))::(aux q)
  | phi::q -> failwith"ne devrait pas arriver"
  in
  List.fold_left (fun x y -> inter x y) (nodes_to_state nodes) (aux (extrait_sous_formule f))
  (* On prend l'intersection de tout les ensembles obtenues avec aux *)

(* Extrait les littéraux d'un ensemble de couple (noeud, ensemble de formule)  *)
let rec litteraux (q: noeud) (now: (noeud* (ltl list)) list) : ltl list = 
  let rec litteraux_aux (ltlset: ltl list) : ltl list = 
    (* Récupère tout les littéraux d'un ensemble de formule ltlset *)
    match ltlset with 
    | [] -> []
    | f::p -> let res = (litteraux_aux p) in
      begin 
        match f with 
        | Atom p  -> if (not (appartient f res)) then (Atom p)::res
        else res
        | Not (Atom p) -> if (not (appartient f res)) then (Not (Atom p))::res
        else res
        | _ -> res
      end
    in
  match now with 
  | [] -> [] 
  | (x,l)::p -> if (x.name = q.name) then ( 
      (litteraux_aux l)@(litteraux q p)
  )
  else (litteraux q p)


(* Construit la valuation pour l'automate de buchi *)
let rec build_valuation (nodes : noeud list) (now : (noeud* (ltl list)) list) : (state * (ltl list)) list =
  match nodes with 
  | [] -> []
  | q::p ->  ({etat = q.name}, litteraux q now)::(build_valuation p now)

(* Construit l'ensemble d'états *)
let rec build_state (nodes : noeud list) : state list = 
  match nodes with 
  | [] -> []
  | q::p -> {etat = q.name}::(build_state p)

(* Récupère le noeud initial dans nodes *)
let rec get_init (nodes : noeud list) : noeud = 
  match nodes with 
  | [] -> failwith"noeud initial non trouvé"
  | x::q -> if (x.name = "init") then x
  else get_init q

let build_lgba (f: ltl) : buchi_automate = 
  let init = {name = "init"} in 
  let (nodes,now,incoming) = create_graph f in 
  {
    q = build_state nodes;
    init = build_init nodes incoming init; 
    transition = build_transition nodes incoming ;
    final = build_final f nodes now; 
    valuation = build_valuation nodes now 
  }

(* On va donc maintenant coder l'intersection entre deux automates de buchi, l'un d'eux sera une
structure de kripke qui aura été transformé en automate de buchi *)

(* Réalise l'opération q1 x q2 (produit cartésien des états) *)
let rec prod_states (q1: state list) (q2: state list) : (state*state) list = 
  let rec prod_cart (q: state) (l: state list) : (state*state) list = 
    match l with 
    | [] -> []
    | y::p -> (q,y)::(prod_cart q p)
  in
  match q1 with 
  | [] -> []
  | x::l -> let res = prod_states l q2 in
    union (prod_cart x q2) res

(* Permet d'obtenir les états initiaux de l'automate produit, I = {(q,q') / q ∈ I1, q' ∈ I2} *)
(* On va donc naturellement utilisé la fonction précédente *)
let prod_init (b1 : buchi_automate) (b2 : buchi_automate) : (state*state) list = 
  prod_states (b1.init) (b2.init)

(* Un état (q,q') est final pour l'automate produit ssi q final pour b1 et q' final pour b2  *)
let prod_final (b1: buchi_automate) (b2:buchi_automate) : (state*state) list = 
  prod_states (b1.final) (b2.final)

(* Récupère l'ensemble des transitions sortantes de q *)
let rec get_transition (q: state) (t: (state * state) list) : (state * state) list = 
  match t with 
  | [] -> []
  | (x,y)::p -> if (x=q) then  (x,y)::(get_transition q p)
  else (get_transition q p)

(* Fusionne deux ensembles de transitions : exemple 
fusion [(q1,q1); (q1;q2)] [(s0,s0);(s0;s1)] renverra
[((q1,s0),(q1,s0)); ((q1,s0),(q1,s1)) ; ((q1,s0),(q2,s0)) ; ((q1,s0), (q2,s1))]*)
let rec fusion (t1: (state * state) list) (t2: (state * state) list) : ((state * state) * (state * state)) list = 
  (* idem mais avec un seul état *)
  let rec fusion_bis (q: (state * state)) (t: (state * state) list) : ((state * state) * (state * state)) list = 
    let (q1,q2) = q in 
    match t with 
    | [] -> []
    | (x,y)::p -> ((q1,x),(q2,y))::(fusion_bis q p)
  in
  match t1 with 
  | [] -> []
  | q::p -> union (fusion_bis q t2) (fusion p t2)


(* Récupère l'ensemble des étiquettes de notre automate de buchi b *)
let get_alphabet (b:buchi_automate) : ltl list = 
  (* récupère les litteraux de la forme Atom "p" d'un ensemble de formule fset *)
  let rec get_litteral (fset : ltl list) : ltl list = 
    match fset with 
    | [] -> []
    | (Atom p)::l | (Not (Atom p))::l -> (Atom p)::(get_litteral l)
    | _::l -> get_litteral l
  in
  let rec aux_alphabet (l: (state * (ltl list)) list) : ltl list = 
    match l with 
    | [] -> []
    | (q,fset)::p -> (get_litteral fset)@(aux_alphabet p)
  
  in aux_alphabet (b.valuation)  

(* Récupère l'ensemble des formules atomiques de la forme Not (Atom "p") dans fset (On renverra une version épurée sans le Not) *)
let rec get_neg (fset: ltl list) : ltl list = 
  match fset with 
  | [] -> []
  | (Not (Atom p))::q -> (Atom p)::(get_neg q)
  | _::q -> get_neg q

(* Renvoie une version modifié de fset, si fset contient une formule de la forme Not (Atom "p"), alors on renvoie
alphabet\{Atom "p"}  *)
let rec modifie_ltlset (fset : ltl list) (alphabet : ltl list ) : ltl list = 
    prive alphabet (get_neg fset)

(* Detecte si un ensemble de formule contient une absurdité du type [Not (Atom "p"); (Atom "p")] *)
let rec absurde (fset : ltl list) : bool = 
  match fset with 
  | [] -> false 
  | (Atom p)::q -> if (appartient (Not (Atom p)) fset) then true 
  else absurde q
  | (Not (Atom p))::q -> if (appartient (Atom p) fset) then true 
  else absurde q
  (* On a ici pas besoin de "regarder en arrière" dans la liste car on la parcourt de gauche a droite *)
  | f::q -> absurde q 

(* Réalise la fonction de transition pour l'automate produit *)
let rec prod_transition (b1: buchi_automate) (b2:buchi_automate) : ((state * state) * (state * state)) list = 
  let states = prod_states (b1.q) (b2.q) in 
  let res = ref [] in 
  let alphabet1 = get_alphabet b1 in let alphabet2 = get_alphabet b2 in 
  let alpha = union alphabet1 alphabet2 in 
  List.iter (fun (q,q') -> 
    (* Rappel : valuation correspond à l'étiquetage des transitions sortants d'un état, ainsi si 
    deux transitions (q1,q2) et (q1',q2') correspondent en valuation_dans_autom1(q1) = valuation_dans_autom2(q2)
    alors on peut ajouter la transition ((q1,q1'),(q2,q2')) *)
    let v1 = List.assoc q (b1.valuation) in let v2 = List.assoc q' (b2.valuation) in
    (* Il y a ici un problème, lorsque la valuation étiquette (Not (Atom "p")), cela 
    signifie que n'importe quelle lettre différente de p permet de prendre la transition *)
    let v1' = modifie_ltlset v1 alpha in let v2' = modifie_ltlset v2 alpha in
    let union_v1v2 = union v1 v2 in
    if ((inter v1' v2') <> [] && (not (absurde union_v1v2))) then (
      let t1 = get_transition q (b1.transition) in 
      let t2 = get_transition q' (b2.transition) in 
      let fus = fusion t1 t2 in 
      res := union (!res) fus
    ) 
    else ()) states;
  !res



(* Réalise la fonction valuation pour l'automate produit *)
let rec prod_valuation (b1: buchi_automate) (b2:buchi_automate) : ((state * state) * (ltl list)) list = 
  let states = prod_states (b1.q) (b2.q) in 
  let res = ref [] in let alphabet1 = get_alphabet b1 in let alphabet2 = get_alphabet b2 in 
  let alpha = union alphabet1 alphabet2 in 
  List.iter (
    fun (q,q') -> 
      let v1 = List.assoc q (b1.valuation) in
      let v2 = List.assoc q' (b2.valuation) in
      let v1' = modifie_ltlset v1 alpha in let v2' = modifie_ltlset v2 alpha in 
      let union_v1v2 = union v1 v2 in
      if ((inter v1' v2') <> [] && not (absurde union_v1v2)) then (
        res := union (!res) ([((q,q'),(union_v1v2))])
      )
      else (res := union (!res) [((q,q'),[])])
  ) states;
  !res


type buchi_automate_product = {
  q : (state * state) list; 
  init : (state * state) list; 
  transition : ((state * state) * (state * state)) list; 
  final : (state * state) list; 
  valuation : ((state * state) * (ltl list)) list
}

let create_product (b1:buchi_automate) (b2:buchi_automate) : buchi_automate_product = 
  {
    q = prod_states (b1.q) (b2.q);
    init = prod_init b1 b2;
    transition = prod_transition b1 b2;
    final = prod_final b1 b2;
    valuation = prod_valuation b1 b2;
  }

(* Début de l'emptiness check *)

let b1_ex:buchi_automate = 
  {
    q= [{etat = "q0"}; {etat = "q1"}; {etat = "q2"}];
    init = [{etat = "q0"}];
    transition = [({etat = "q0"},{etat = "q0"}); ({etat = "q0"}, {etat = "q1"}); ({etat = "q1"}, {etat = "q1"}); ({etat = "q1"}, {etat = "q2"}); ({etat = "q2"}, {etat = "q1"});({etat = "q2"}, {etat = "q0"})];
    final = [{etat = "q2"}];
    valuation = [({etat = "q0"}, [Atom "p"]); ({etat = "q1"}, [Atom "q"]); ({etat = "q2"}, [Atom "p"])] 
  }

let b2_ex: buchi_automate = 
  {
    q= [{etat = "s0"}; {etat = "s1"}];
    init = [{etat = "s0"}];
    transition = [({etat = "s0"},{etat = "s0"}); ({etat = "s0"},{etat = "s1"}); ({etat = "s1"},{etat = "s1"}); ({etat = "s1"},{etat = "s0"})];
    final = [{etat = "s0"}];
    valuation = [({etat = "s0"},[Atom "q"]) ; ({etat = "s1"},[Atom "p"])] 
  }

(* Fonction donné par le doc : https://www.cs.cmu.edu/~15414/f17/lectures/18-ltl.pdf *)
(* Récupère l'ensemble des états atteints en un coup depuis q avec t(transition) *)
let rec get_state_set (q: ((state*state))) (t: ((state * state)*(state * state)) list) : (state*state) list = 
  match t with 
  | [] -> []
  | (x,y)::p -> if (x=q) then  y::(get_state_set q p)
  else (get_state_set q p)


exception Found

let rec innerdfs (q: (state*state)) (outervisited : (state*state) list) (innervisited : (state*state) list) (b: buchi_automate_product) : unit = 
  let innervisited' = q::innervisited in 
  List.iter (fun q' -> if (appartient q' outervisited) then (raise Found)
  else if (not (appartient q' innervisited' )) then (innerdfs q' outervisited innervisited' b)) (get_state_set q (b.transition))


let rec outerdfs (q:(state*state)) (visited : (state*state) list) (b: buchi_automate_product) : unit = 
  let visited' = q::visited in 
  List.iter (fun q' -> if (not (appartient q' visited')) then (outerdfs q' visited' b)) (get_state_set q (b.transition));
  if (appartient q (b.final)) then (innerdfs q visited' [] b)
  else ()

let is_empty (b: buchi_automate_product) : bool = 
  let res = ref true in 
  List.iter (fun q -> 
    try
      outerdfs q [] b 
    with
    | Found -> res := false
    ) (b.init);
  !res

let model_checker (k: kripke_struct) (f: ltl) : bool = 
  let b2 = kripke_to_buchi k in 
  let b1 = build_lgba (fnn (Not f)) in 
  let product = create_product b1 b2 in 
  ((is_empty product))


(* ----------------- *)
(* Tests et exemples *)
(* ----------------- *)
let p0 = { etat = "0" }
let p1 = { etat = "1" }

let test_k : kripke_struct = 
  {
  init = [p0];
  q = [p0; p1];
  transition = [(p0, p1); (p1, p1)];
  valuation = [
    (p0, [Atom "a"]);
    (p1, [Atom "b"])
  ];
}

let formule1 = G (F (Atom "b"))
(* Celle ci est censé être vrai dans la structure de kripke *)

let formule2 = F (Atom "b")
(* Celle ci aussi *)

let formule3 = G (Atom "a")
(* Celle la doit être fausse *)


(* Second exemmple *)
let s0 = { etat = "0" }
let s1 = { etat = "1" }
let s2 = { etat = "2" }

let test_k2 : kripke_struct = 
  {
  init = [s0];
  q = [s0; s1; s2];
  transition = [
    (s0, s1);
    (s1, s2);
    (s2, s2)
  ];
  valuation = [
    (s0, [Atom "p"]);
    (s1, [Atom "p"]);
    (s2, [Atom "q"])
  ];
}

(* Doit être vrai *)
let formule_t1 = U (Atom "p", Atom "q")

(* Doit être fausse *)
let formule_t2 = G (Atom "p")

(* Doit être vrai *)
let formule_t3 = F (Atom "q")

(* Doit être fausse *)
let formule_t4 = U (Atom "p", Atom "r")


let q0 = {etat = "q0"}
let q1 = {etat = "q1"}
let q2 = {etat = "q2"}

(* Test d'un digicode *)
let test_k3 : kripke_struct = 
  {
  init = [q0];
  q = [q0; q1; q2];
  transition = [
    (q0, q1);
    (q1, q2);
    (q2, q2)
  ];
  valuation = [
    (q0, [Atom "saisir_code"]);
    (q1, [Atom "code_bon"]);
    (q2, [Atom "deverouiller"])
  ];
}

let implique (f1:ltl) (f2:ltl) = (*f1 -> f2*) Or (Not f1, f2)

let formule_pour_que_digicode_correct = (F (And ((Atom "code_bon"),(X (Atom "deverouiller")))))
(* Un jour (F), on aura saisi le bon code (code_bon) et (and) le prochain état (X) vérifiera dévérouiller *)




