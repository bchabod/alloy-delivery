open util/integer
open util/ordering[Time] as to
open util/boolean

/********************************* Signatures *********************************/

/**
 * Signature Time pour simuler le temps.
 */
sig Time
{
}



/**
 * Signature de l'objet Drone
 * Attributs :
 *    coordonnees : coordonnees actuelles du drone
 */
sig Drone
{
    coordonnees : Coordonnees one -> Time,
	batterie : Int one -> Time,
	commande : Commande lone -> Time,
	coordonneesCible : Coordonnees lone -> Time,
	capaciteMax : Int, 
	coordReceptaclesVisites : Coordonnees set -> Time
}

/**
 * Signature de l'objet Receptacle
 * Attributs :
 *    coordonnees : coordonnees du receptables
 *    receptaclesVoisins : tous les receptables voisins de ce receptable
 */
sig Receptacle
{
    coordonnees : Coordonnees,
	capaciteMax : Int, 
	contenanceActuelle : Int one -> Time ,
	receptaclesVoisins : some Receptacle
}

/**
 * Signature de l'objet Entrepot
 * Attributs :
 *    coordonnees : coordonnees de l'entrepot
 *    receptaclesVoisins : tous les receptables voisins de cet entrepot
 */
sig Entrepot
{
	coordonnees : Coordonnees,
	receptaclesVoisinsEntrepot : some Receptacle,
	commandes: some Commande
}

/**
 * Signature de l'objet Coordonnees
 * Attributs :
 *    x : coordonnee X (entier) de cette coordonnee
 *    Y : coordonnee Y (entier) de cette coordonnee
 */
sig Coordonnees
{
    x : Int,
    y : Int
}

/**
 * Signature de l'objet Commande
 * Attributs :
 *	  coordonneesLivraison : Coordonnees ou doit etre effectuee la livraison
 */ 
sig Commande
{
	coordonneesLivraison : Coordonnees,
	poids: Int,
	affectee : Bool one -> Time
}
/********************************* Fonctions *********************************/

/** 
  * Calcule la valeur absolue d'un entier
  * Retourne : la valeur absolue de l'entier X
  */
fun abs[x: Int]: Int {
    x >= 0 => x else x.mul[-1]
}

/** 
  * Calcule la valeur max entre deux entiers
  * Retourne : la valeur max entre a et b
  */
fun max[a, b: Int]: Int {
	a > b => a else b
}

/********************************* Faits *********************************/

/** 
  * Ensemble des faits pour placer les elements avec leurs coordonnees
  */
fact invCoordonnees
{
	initInstances
	predCoordonnees

	receptaclesVoisins
	poidsCommandes
}


fact initCapacites
{
	capacitesReceptacles
	capacitesDrones
}


/**
 * Sequences d'execution
 */
fact traces 
{
	// Post-Condition du programme
	init [to/first]

	// Execution
	all t: Time - to/last 
		| let t' = t.next 
			| all drone: Drone 
				|  (charger[t, t', drone] || rechargerBatterie[t, t', drone] || livrer[t, t', drone] || deplacerDroneVersCommande[t, t', drone] || deplacerDroneVersEntrepot[t, t', drone] || skip[t, t', drone])
	
	all t: Time - to/last 
		| let t' = t.next 
			| all r: Receptacle
				| majReceptacle[t, t', r]
	
	all t: Time - to/last 
		| let t' = t.next 
			| all c: Commande
				| majCommande[t, t', c]

	// Post-Condition du programme
	all drone: Drone | #drone.commande.to/last = 0 && some e:Entrepot | drone.coordonnees.to/last = e.coordonnees
	all c: Commande | c.affectee.to/last = {True}
}

/**
 * Initialisation à T0
 */
pred init [t: Time]
{
	// Tous les drones sont sur un entrepot
	all d: Drone | some e: Entrepot | d.coordonnees.t = e.coordonnees

	// Toutes les commandes appartiennent a l'entrepot
	all c:Commande | one e:Entrepot | c in e.commandes

	// Pas de commande à prendre en charge en début
	all d: Drone | #d.commande.t = 0 && #d.coordonneesCible.t = 0 && #d.coordReceptaclesVisites.t = 0

	// Toutes les commandes sont non affectées
	all c: Commande | c.affectee.t = {False}
	

	// Initialise la batterie au max
	all d: Drone | d.batterie.t = 3

	//on initialise les contenances des receptacles
	all r: Receptacle | r.contenanceActuelle.t = 0
}

/**
 * Opération : Charge une commande
 * Précondition : Drone sur entrepot, sans commande, avec batterie pleine, avec presence de commandes à traiter
 */
pred charger [t, t': Time, drone: Drone] 
{
	// Précondition
	(one e: Entrepot | drone.coordonnees.t = e.coordonnees && some c: e.commandes | c.affectee.t = {False}) && drone.batterie.t = 3 && #drone.commande.t = 0

	// Affectation de la commande
	some c: Commande, e: Entrepot | c in e.commandes && c.affectee.t = {False} && drone.commande.t' = c && c.affectee.t' = {True}

	// Commande ne pouvant être partagée avec d'autres drones
	no d: Drone | d != drone && d.commande.t' = drone.commande.t'

	// Initialisation du réceptacle cible du drone au réceptacle le plus proche, qui est dans l'ilot de la commande
	some r: Receptacle | drone.coordonneesCible.t' = r.coordonnees && r.coordonnees.positionVoisin[drone.coordonnees.t]

	// Nouveau parcours à effectuer
	#drone.coordReceptaclesVisites.t' = 0

	// Nouvelles valeurs
	drone.coordonnees.t' = drone.coordonnees.t
	drone.batterie.t' = drone.batterie.t
}

/**
 * Opération : Recharge de batterie
 * Précondition : Drone sur son réceptacle cible et possède une batterie < 3 (non pleine)
 */
pred rechargerBatterie [t, t': Time, drone: Drone] 
{
	// Précondition
	drone.coordonnees.t = drone.coordonneesCible.t && drone.batterie.t < 3

	// Nouvelles valeurs
	drone.coordonnees.t' = drone.coordonnees.t
	drone.coordonneesCible.t' = drone.coordonneesCible.t
	drone.coordReceptaclesVisites.t' = drone.coordReceptaclesVisites.t
	drone.commande.t' = drone.commande.t
	drone.batterie.t' = drone.batterie.t.add[1]
}

/**
 * Opération : Déplacement de drone
 * Précondition : Possède une commande, n'est pas sur la livraison et :
 *	- Soit le drone se situe sur la cible mais avec une batterie pleine (si non pleine il doit se recharger)
 *  - Soit le drone ne se situe pas sur la cible
 */
pred deplacerDroneVersCommande [t, t': Time, drone: Drone] 
{
	// Précondition
	((drone.coordonnees.t = drone.coordonneesCible.t && drone.batterie.t = 3) || (drone.coordonnees.t != drone.coordonneesCible.t))
	#drone.commande.t = 1 && drone.commande.t.coordonneesLivraison != drone.coordonnees.t	

	// On regarde si la cible a ete atteinte
	drone.coordonnees.t = drone.coordonneesCible.t => {
		// On ajoute les coordonnees du receptacle au chemin parcouru
		drone.coordReceptaclesVisites.t' = drone.coordReceptaclesVisites.t + drone.coordonneesCible.t
		// Le receptacle cible change
		some r: Receptacle 
			| r.coordonnees.positionVoisin[drone.coordonnees.t] && r.coordonnees not in drone.coordReceptaclesVisites.t && drone.coordonneesCible.t' = r.coordonnees
	} else {
		// On garde le même réceptacle cible
		drone.coordonneesCible.t' = drone.coordonneesCible.t
		// On garde le même chemin
		drone.coordReceptaclesVisites.t' = drone.coordReceptaclesVisites.t
	}

	// On se dirige vers la cible a l'instant t'
	(
		(drone.coordonneesCible.t'.x > drone.coordonnees.t.x && drone.coordonnees.t'.x = drone.coordonnees.t.x.add[1] && drone.coordonnees.t'.y = drone.coordonnees.t.y)
  	 || (drone.coordonneesCible.t'.x < drone.coordonnees.t.x && drone.coordonnees.t'.x = drone.coordonnees.t.x.sub[1] && drone.coordonnees.t'.y = drone.coordonnees.t.y)
     || (drone.coordonneesCible.t'.y > drone.coordonnees.t.y && drone.coordonnees.t'.y = drone.coordonnees.t.y.add[1] && drone.coordonnees.t'.x = drone.coordonnees.t.x)
     || (drone.coordonneesCible.t'.y < drone.coordonnees.t.y && drone.coordonnees.t'.y = drone.coordonnees.t.y.sub[1] && drone.coordonnees.t'.x = drone.coordonnees.t.x)
	)

	// On vérifie qu'un autre drone ne souhaite pas aller aux futures coordonnees, sauf s'il s'agit d'un entrepot
	no d: Drone | d != drone && d.coordonnees.t' = drone.coordonnees.t' && no e: Entrepot | e.coordonnees = drone.coordonnees.t'

	// Diminution de la batterie
	drone.batterie.t' = drone.batterie.t.sub[1]

	drone.commande.t' = drone.commande.t
}	

/**
 * Opération : Déplacement retour d'un drone
 * Précondition : Plus de commande et n'est pas sur un entrepot
 */
pred deplacerDroneVersEntrepot [t, t': Time, drone: Drone] 
{
	// Prédicat
	#drone.commande.t = 0 && no e: Entrepot | drone.coordonnees.t = e.coordonnees

	// On regarde si la cible change
	drone.coordonnees.t = drone.coordonneesCible.t => {
		// On enleve le réceptacle au chemin a parcourir
		drone.coordReceptaclesVisites.t' = drone.coordReceptaclesVisites.t - drone.coordonneesCible.t
		// La cible change : soit le receptacle voisin dans l'historique, soit un entrepot si historique vide
		#drone.coordReceptaclesVisites.t' > 0 => {
 			some cible: Coordonnees 
				| cible.positionVoisin[drone.coordonnees.t] && cible in drone.coordReceptaclesVisites.t && drone.coordonneesCible.t' = cible
		} else {
			some e: Entrepot
				| e.coordonnees.positionVoisin[drone.coordonnees.t] && drone.coordonneesCible.t' = e.coordonnees
		}
	} else {
		// On garde la meme cible
		drone.coordonneesCible.t' = drone.coordonneesCible.t
		// On garde le même chemin
		drone.coordReceptaclesVisites.t' = drone.coordReceptaclesVisites.t
	}

	// On se dirige vers la cible a l'instant t'
	(
		(drone.coordonneesCible.t'.x > drone.coordonnees.t.x && drone.coordonnees.t'.x = drone.coordonnees.t.x.add[1] && drone.coordonnees.t'.y = drone.coordonnees.t.y)
  	 || (drone.coordonneesCible.t'.x < drone.coordonnees.t.x && drone.coordonnees.t'.x = drone.coordonnees.t.x.sub[1] && drone.coordonnees.t'.y = drone.coordonnees.t.y)
     || (drone.coordonneesCible.t'.y > drone.coordonnees.t.y && drone.coordonnees.t'.y = drone.coordonnees.t.y.add[1] && drone.coordonnees.t'.x = drone.coordonnees.t.x)
     || (drone.coordonneesCible.t'.y < drone.coordonnees.t.y && drone.coordonnees.t'.y = drone.coordonnees.t.y.sub[1] && drone.coordonnees.t'.x = drone.coordonnees.t.x)
	)

	// On vérifie qu'un autre drone ne souhaite pas aller aux futures coordonnees, sauf s'il s'agit d'un entrepot
	no d: Drone | d != drone && d.coordonnees.t' = drone.coordonnees.t' && no e: Entrepot | e.coordonnees = drone.coordonnees.t'

	// Diminution de la batterie
	drone.batterie.t' = drone.batterie.t.sub[1]

	// Nouvelles valeurs
	drone.commande.t' = drone.commande.t
}

pred skip [t, t': Time, drone: Drone] 
{
	// Nouvelles valeurs
	drone.coordonnees.t' = drone.coordonnees.t
	drone.coordonneesCible.t' = drone.coordonneesCible.t
	drone.coordReceptaclesVisites.t' = drone.coordReceptaclesVisites.t
	drone.commande.t' = drone.commande.t
	drone.batterie.t' = drone.batterie.t
}

pred majCommande [t, t' : Time, c : Commande] 
{
	(no d: Drone | d.commande.t' = c) => {
		// On conserve la valeur affectee
		c.affectee.t' = c.affectee.t
	} else {
		// La commande est affectée
		c.affectee.t' = {True}
	}		
}

/**
 * Opération : Livrer une commande
 * Précondition : Batterie pleine (= 3) && Sur les coordonnees de livraison && Presence d'une commande
 */
pred livrer [t, t': Time, drone: Drone] 
{
	// Précondition
	#drone.commande.t = 1 && drone.coordonnees.t = drone.commande.t.coordonneesLivraison && drone.batterie.t = 3

	// Nouvelles valeurs
	drone.coordonnees.t' = drone.coordonnees.t
	drone.coordonneesCible.t' = drone.coordonneesCible.t
	drone.coordReceptaclesVisites.t' = drone.coordReceptaclesVisites.t
	drone.batterie.t' = drone.batterie.t

	
	#drone.commande.t' = 0
}

/**
* Propage la contenance du receptacle aux coordonnees c à travers le temps.
*/
pred majReceptacle [t, t' : Time, r : Receptacle] 
{
	//soit on trouve un drone qui livre et on add le poids
	(one d: Drone | #d.commande.t = 1 && d.coordonnees.t = d.commande.t.coordonneesLivraison && d.batterie.t = 3 && r.coordonnees = d.coordonnees.t &&
		 r.contenanceActuelle.t' = r.contenanceActuelle.t.add[d.commande.t.poids])
	<=> not
	//soit on propage ce qu'il y avait avant, ou on le vide aléatoirement
		( r.contenanceActuelle.t' = r.contenanceActuelle.t || ( r.contenanceActuelle.t' = 0))
}
 
/********************************* Predicats *********************************/

/** 
  * Vérifie que deux coordonnees sont egales
  */
pred coordonneesEgales[c0,c1 : Coordonnees]
{
	c0.x = c1.x && c0.y = c1.y
}

/** 
  * Initialise le nombre d'instances des objets
  */
pred initInstances
{
	one Entrepot
	#Drone = 2	// DNB
	#Receptacle = 5	// RNB
}

/** 
  * Ensemble des predicats qui contraignent les coordonnees
  */
pred predCoordonnees
{
	coordonneesUniques
	coordonneesReceptacles
	coordonneesEntrepot
	coordonneesDrones
	coordonneesCommandes
}

/** 
  * Verifie que les instances de Coordonnees sont sur des cases differentes
  */
pred coordonneesUniques
{
	no c0, c1 : Coordonnees | (c0 != c1 && c1.coordonneesEgales[c0])
}
/** 
  * Verifie que les receptacles soient sur des coordonnees differentes
  */
pred coordonneesReceptacles
{
	no r0, r1 : Receptacle | (r0 != r1 && r0.coordonnees = r1.coordonnees)
}

/** 
  * Verifie que les receptacles ne soient pas sur les coordonnees des entrepots
  */
pred coordonneesEntrepot
{
	no r : Receptacle, e : Entrepot | r.coordonnees = e.coordonnees
}

/** 
  * Verifie que les drones ne soient pas sur les memes coordonnees, a l'exception des entrepots,
  * qui peuvent heberger plusieurs drones.
  */
pred coordonneesDrones
{
//	no d0, d1 : Drone | (d0 != d1  && d0.coordonnees = d1.coordonnees && (no e0 : Entrepot | d0.coordonnees = e0.coordonnees))
}

/** 
  * Verifie que les commandes sont sur des receptacles
  */
pred coordonneesCommandes
{
	all c: Commande | some r: Receptacle | c.coordonneesLivraison = r.coordonnees
}

/** 
  * Verifie que deux coordonnees soient au plus d'une distance de 3 cases (distance de manhattan)
  */
pred positionVoisin[c0, c1 : Coordonnees]
{
	abs[c0.x.sub[c1.x]].add[abs[c0.y.sub[c1.y]]] =< 3
}

/** 
  * Verifie que deux coordonnees soient au plus d'une distance de 3 cases (distance de manhattan)
  */
pred receptaclesVoisins
{
	// Decommenter la ligne ci-dessous pour forcer plusieurs chemins en sortie de l'entrepot
	//all e0 : Entrepot | #e0.receptaclesVoisins = 2

	// Associe des receptacles voisins aux entrepots
	all e0 : Entrepot | all r0: e0.receptaclesVoisinsEntrepot | e0.coordonnees.positionVoisin[r0.coordonnees] 

	// Empeche un receptacle d'etre son propre voisin
	all r0 : Receptacle 
		| !(r0 in r0.receptaclesVoisins)

	// Associe pour chaque receptacle ses receptacles voisins
	all r0: Receptacle | all r1 : r0.receptaclesVoisins | r1.coordonnees.positionVoisin[r0.coordonnees] && r0 in r1.receptaclesVoisins

	// Verifie que chaque receptacle soit accessible depuis les entrepots
    all e0 : Entrepot, r0 : Receptacle 
		| some r1 : e0.receptaclesVoisinsEntrepot 
			| r0 in r1.*receptaclesVoisins
}



pred capacitesReceptacles
{
	all r : Receptacle | r.capaciteMax = 12 //RCAP
}

pred capacitesDrones
{
	all d : Drone | d.capaciteMax = 5 //DCAP
}

//on définit le poids des Commandes
pred poidsCommandes
{
	all c: Commande | c.poids >= 1 && c.poids <= 5 
}


/********************************* Assertions *********************************/

/**
 * Verifie qu'il n'existe pas deux drones sur les memes coordonnees, a l'exception
 * des entrepots.
 */
assert assertCoordonneesDrones 
{
	no d0 : Drone, t : Time |
		(no e : Entrepot | e.coordonnees = d0.coordonnees.t) 
 	 &&	(some d1 : Drone | d0 != d1 && d0.coordonnees.t = d1.coordonnees.t)
}

check assertCoordonneesDrones for 15 but 1 Entrepot, 2 Drone, 5 Receptacle, 4 Commande, 6 int, 10 Time

/**
 * Verifie la tolerance d'un cas particulier : 2 receptacles sont voisins d'un
 * entrepot, sans etre voisins entre eux.
 * /!\ : Fonctionne que si la cardinalite des receptacles en sortie de l'entrepot
 * est > 1.
 */
assert assertReceptablesVoisinsEntrepotMaisPasEntreEux 
{
	some r0, r1 : Receptacle, e0 : Entrepot
	 | r0 != r1 && 
	   !r0.coordonnees.positionVoisin[r1.coordonnees] && 
	   e0.coordonnees.positionVoisin[r0.coordonnees] &&
	   e0.coordonnees.positionVoisin[r1.coordonnees]
}
check assertReceptablesVoisinsEntrepotMaisPasEntreEux for 8 but 6 int

//mise en évidence que ça ne marche pas pour le moment
assert receptacleVoisinSontVoisins
{
	all r:Receptacle | r.receptaclesVoisins.coordonnees.positionVoisin[r.coordonnees]
}

check receptacleVoisinSontVoisins for 7 but 6 int

/**
 * Vérification : Une commande ne peut avoir l'état "non affectée" et être reliée à un drone.
 */
assert assertCommandeEtatErrone
{
	no c : Commande, t : Time, d : Drone |
		c.affectee.t = {False} && #d.commande.t = 1 && d.commande.t = c
}

check assertCommandeEtatErrone for 15 but 2 Drone, 5 Receptacle, 6 int, 1 Entrepot, 2 Commande

/**
 * Vérification : Deux drones ne peuvent partager une même commande à un instant T.
 */
assert assertCommandesPartagees
{
	no d0, d1 : Drone, t : Time |
		d0 != d1 && #d0.commande.t = 1 && d0.commande.t = d1.commande.t
}

check assertCommandesPartagees for 15 but 2 Drone, 5 Receptacle, 6 int, 1 Entrepot, 2 Commande

/********************************* Lancements *********************************/

/**
 * Predicat vide permettant la simulation
 */ 
pred go
{
	// Placement de l'entrepôt au centre de la carte
	one e : Entrepot | e.coordonnees.x = 0 && e.coordonnees.y = 0

	// Une commande rapprochee
	//one c: Commande, r: Receptacle | c.coordonneesLivraison.x = 0 && c.coordonneesLivraison.y = 2 && c.coordonneesLivraison = r.coordonnees

	// Limite sur la taille de la carte
	all c : Coordonnees | c.x <= 8 && c.x >= -8 && c.y <= 8 && c.y >= -8
}

run go for 10 but 2 Drone, 5 Receptacle, 6 int, 1 Entrepot

