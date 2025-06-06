
# Projet-TIPE : Model-Checking

## Objectif

Ce projet a pour but de mettre en œuvre un **vérificateur de modèle (model checker)** en utilisant la logique temporelle linéaire (LTL) dans le langage OCaml.  
L'objectif est de déterminer si une **structure de Kripke** satisfait une formule LTL donnée à l'aide d'automates de Büchi.
L'interêt principal est de modéliser un algorithme à l'aide d'une structure de Kripke, et de montrer qu'il vérifie une certaine formule LTL (un invariant par exemple si on veut montrer la correction de notre algorithme).

---

## Fonctionnalités principales

Le projet s'articule autour de 6 grandes étapes :

1. **Implémentation de la logique LTL**
   - Représentation de formules LTL en OCaml.
   - Conversion en **forme normale négative (FNN)**.

2. **Structures de Kripke et automates de Büchi**
   - Définitions.

3. **Traduction en automate de Büchi**
   - Conversion d'une structure de Kripke en un automate de Büchi.

4. **Conversion LTL → automate de Büchi**
   - Génération d’un automate de Büchi acceptant toutes les exécutions satisfaisant une formule LTL donnée.

5. **Intersection d'automates de Büchi**
   - Calcul de l’intersection entre deux automates de Büchi.

6. **Test de vacuité**
   - Vérification si le langage l’automate résultant est vide ou non.
---

On veut savoir si le modèle M vérifie une propriété phi.

B(M) représente l'automate de Büchi associé au modèle M.

B(Non phi) représente l'automate de Büchi associé à la formule (Non phi).

(cf II) pour la définition d'un automate de Büchi)

![image](https://github.com/user-attachments/assets/af84ae28-bfb3-470d-a731-67118c35c74c)

---
## I) Implémentation de la logique LTL
On adopte une définition inductive de la logique LTL :

![image](https://github.com/user-attachments/assets/21fb9eda-be0a-4e36-a052-06436ae732e3)

L'opérateur X pour neXt (Dans l'état suivant, on vérifie phi): 

![image](https://github.com/user-attachments/assets/8dc27196-e9f1-441d-97a7-8db49a8d4b05)

L'opérateur F pour Finally (Il existe un état que l'on va atteindre dans le futur qui vérifie phi):

![image](https://github.com/user-attachments/assets/f9f6e2c1-d97b-49e8-b364-4752a68bed97)

L'opérateur G pour Globally (phi est vrai partout):

![image](https://github.com/user-attachments/assets/ba6e4b16-3cd9-49a2-9bba-45b00c30d326)

L'opérateur U pour Until (phi1 est vrai jusqu'à ce qu'on vérifie phi2 et après on fait ce que l'on veut):

![image](https://github.com/user-attachments/assets/0a35177f-f608-416c-8356-6570f9ff2980)

L'opérateur R pour Release (phi2 est vrai jusqu'à ce qu'on vérifie phi2 et phi1 et après on fait ce que l'on veut):

![image](https://github.com/user-attachments/assets/74a110c9-2f24-49dd-bf9e-b6cd42a7e2fa)

---

Une formule LTL est dite sous forme normale négative si :
- L'opérateur négation est appliqué seulement à des propositions atomiques (des variables).
- Les opérateurs G et F n'apparaissent pas.

Exemple : 

![image](https://github.com/user-attachments/assets/9333f09b-c760-4827-b1df-e29778b0e57a)

---

Pour "pousser" la négation et supprimer F et G on utilise les Lois de De Morgan ainsi que les règles suivants : 

![image](https://github.com/user-attachments/assets/270798b5-2811-42f4-a13c-46da114ce2d1)

## II) Structures de Kripke et automates de Büchi

Exemple et définition d'une structure de Kripke : 

Ici AP désigne l'ensemble des propositions atomiques (variables).

Ici :
- Q désigne un ensemble d'états.
- I désigne un ensemble d'états initiaux.
- -> désigne un ensemble de transitions.
- L désigne un ensemble d'étiquettes. (Une étiquette est placé sur un état mais on peut le voir comme : toutes les transitions sortantes de cet état sont étiquettés par l'étiquette du noeud actuelle)

![image](https://github.com/user-attachments/assets/6b432d8f-aed3-4d27-b0a3-02caed2081b4)

---

Pour les automates de Büchi : 

Où F est un ensemble d'états finaux.

![image](https://github.com/user-attachments/assets/289cc5a4-877b-4df1-9292-9c66f146f477)

---

## III) Traduction en automate de Büchi

![image](https://github.com/user-attachments/assets/de2f95bf-6b8d-46ce-a1ef-0be5c54b9d63)

Exemple : 

![image](https://github.com/user-attachments/assets/271df78b-3f85-4b02-a433-ebf49304f896)


---

## IV) Conversion LTL → automate de Büchi

Je conseille de regarder l'animation page 10 du diapo pour comprendre.

Règles utilisées : 

![image](https://github.com/user-attachments/assets/713db73f-5e8a-4d15-92f2-7e89ce476005)

---

Les doubles flèches sur le diapo représentent un pas dans le temps, on avance à l'état suivant (car on à un X (pour neXt))

---

Exemple : automate de Büchi pour la formule Non (G (F p))

![image](https://github.com/user-attachments/assets/3ea0db47-c7e1-4c37-84b4-4eb1a4e7e9cb)


## V) Intersection d'automates de Büchi

Pour l'intersection, on fait comme pour l'intersection d'automates finis, mais lorsque l'intersection des étiquettes entre deux états est vide, on n'accepte pas les transitions.

![image](https://github.com/user-attachments/assets/99bfd707-4d65-4d90-9b6a-e2dea657b03e)

---

Exemple : 

![image](https://github.com/user-attachments/assets/f6698c70-330f-4efe-88fd-53f4cca4fbb5)


![image](https://github.com/user-attachments/assets/13e3e459-de66-48d2-aad9-e1049a72ace1)

---

## VI) Test de vacuité
> [!IMPORTANT]
> Rappel : la condition d'acceptation pour un mot infini dans un automate de Büchi est que l'on passe infiniement souvent par un état de F.

Ainsi, l'idée est la suivante, depuis chacun des états initiaux, on réalise un parcours en profondeur depuis celui-ci, dès que l'on rencontre un état final, on lance un parcours en profondeur depuis celui-ci afin de chercher un cycle.

Voici les 3 algorithmes utilisées : 

![image](https://github.com/user-attachments/assets/c874800e-05b8-461d-8b55-2d3d876fd8d4)

![image](https://github.com/user-attachments/assets/87a1c4ca-5967-491a-9c53-ca446e42ed8f)

![image](https://github.com/user-attachments/assets/85d8f49c-7ad4-42c5-9f47-20a7855d2fa8)

---






