open util/integer
open util/ordering[Time] as to

/********************************* Signatures *********************************/

/**
 * Signature Time pour simuler le temps.
 */
sig Time
{
}

/**
 * Signature de l'objet Chemin
 * Attributs :
 *    receptaclesVisites : ensemble (0..*) des réceptacles qui ont déjà été parcourus
 */
/*
sig Chemin
{
	receptaclesVisites : set Receptacle
}*

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
//	capaciteMax : Int, 
//	contenanceActuel : Int,
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
//	capaciteMax : Int, 
//	contenanceActuel : Int
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

	//la liste de Commande évolue au fil du temps
	commandes:  Commande some -> Time,
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
//	contenanceActuelle: Int
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
}

/*
fact initCapacites
{
	capacitesReceptacles
	capacitesDrones
	batterieDrones
}
*/

/**
 * Sequences d'execution
 */
fact traces 
{
	init [to/first]
	all t: Time - to/last 
		| let t' = t.next 
			| all drone: Drone 
				|  (rechargerBatterie[t, t', drone] || livrer[t, t', drone] || deplacerDroneVersCommande[t, t', drone] || deplacerDroneVersEntrepot[t, t', drone] || skip[t, t', drone])
//rechargerBatterie[t, t', drone] || livrer[t, t', drone] || deplacerDrone[t, t', drone]
	all drone: Drone | #drone.commande.to/last = 0 && some e:Entrepot | drone.coordonnees.to/last = e.coordonnees
}

/**
 * Initialisation à T0
 */
pred init [t: Time]
{
	// Tous les drones sont sur un entrepot
	all d: Drone | some e: Entrepot | d.coordonnees.t = e.coordonnees

	//toutes les commandes sont a l'entrepot
	all c:Commande | one e:Entrepot | c in e.commandes.t
	
	//une commande ne peut pas être partagée entre 2 drones 
    no d0, d1: Drone | (d1 != d0 && d0.commande.t = d1.commande.t)
	
	// Tous les drones se chargent d'une commande TODO : à vérifier
	all d: Drone | #d.commande.t = 1
	
	// Initialisation du réceptacle cible des drones au réceptacle le plus proche, qui est dans l'ilot de la commande
	all d: Drone, e: Entrepot | one r:Receptacle | d.coordonneesCible.t = r.coordonnees && r.coordonnees.positionVoisin[e.coordonnees]

	// Initialise la batterie au max
	all d: Drone | d.batterie.t = 3

	// Les chemins sont nuls pour les drones à T0
	all d: Drone | #d.coordReceptaclesVisites.t = 0
	
	// TODO : peut être mettre ailleurs, à voir
	// Les chemins appartiennent seulement aux drones
	//all c: Chemin | some d: Drone | d.cheminTraverse.t = c


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
 * Précondition : 
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

/**
 * Opération : Livrer une commande
 * Précondition : Batterie non pleine (on vient d'arriver), ie < 3 && Sur les coordonnees de livraison
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

	// TODO : Mettre commande à 0 -> commande doit dépendre du temps aussi !
	#drone.commande.t' = 0
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


/*
pred capacitesReceptacles
{
	all r : Receptacle | r.capaciteMax = 7 && r.contenanceActuel = 0//RCAP
}

pred capacitesDrones
{
	all d : Drone | d.capaciteMax = 2 && d.contenanceActuel = 0 //DCAP
}

pred batterieDrones
{
	all d : Drone | d.batterie = 3
}
*/

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

check assertCoordonneesDrones for 15  but 3 Drone, 6 Receptacle, 5 Time, 4 Commande, 6 int

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

