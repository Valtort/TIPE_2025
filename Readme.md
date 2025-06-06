
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

B(M) représente l'automate de Büchi associé au modèle M.\\
B(Non phi) représente l'automate de Büchi associé à la formule (Non phi).

(cf II) pour la définition d'un automate de Büchi)

![image](https://github.com/user-attachments/assets/af84ae28-bfb3-470d-a731-67118c35c74c)


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


