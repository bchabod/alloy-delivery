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
sig Chemin
{
	receptaclesVisites : set Receptacle
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
	commande : lone Commande,
	receptacleCible : Receptacle lone -> Time,
//	capaciteMax : Int, 
//	contenanceActuel : Int,
	cheminTraverse : Chemin one -> Time
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
	receptaclesVoisinsEntrepot : some Receptacle
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
				| rechargerBatterie[t, t', drone] || livrer[t, t', drone] || deplacerDrone[t, t', drone]
}

/**
 * Initialisation à T0
 */
pred init [t: Time]
{
	// Tous les drones sont sur un entrepot
	all d: Drone | some e: Entrepot | d.coordonnees.t = e.coordonnees

	// TODO : une commande ne peut etre partagee par plusieurs drones
	// Tous les drones se chargent d'une commande TODO : à vérifier
	all d: Drone | #d.commande = 1
	
	// Initialisation du réceptacle cible des drones au réceptacle le plus proche, qui est dans l'ilot de la commande
	// TODO : vérifier cette ligne, elle me parait extremement louche et fumeuse.
	// /!\/!\ 
	all d: Drone, e: Entrepot | one r:Receptacle | d.receptacleCible.t = r && r.coordonnees.positionVoisin[e.coordonnees]

	// Initialise la batterie au max
	all d: Drone | d.batterie.t = 3

	// Les chemins sont nuls pour les drones à T0
	all d: Drone | #d.cheminTraverse.t.receptaclesVisites = 0
	
	// TODO : peut être mettre ailleurs, à voir
	// Les chemins appartiennent seulement aux drones
	all c: Chemin | some d: Drone | d.cheminTraverse.t = c
}

/**
 * Opération : Recharge de batterie
 * Précondition : Drone sur son réceptacle cible et possède une batterie < 3 (non pleine)
 */
pred rechargerBatterie [t, t': Time, drone: Drone] 
{
	// Précondition
	drone.coordonnees.t = drone.receptacleCible.t.coordonnees && drone.batterie.t < 3

	// Nouvelles valeurs
	drone.coordonnees.t' = drone.coordonnees.t
	drone.receptacleCible.t' = drone.receptacleCible.t
	drone.cheminTraverse.t' = drone.cheminTraverse.t

	drone.batterie.t' = drone.batterie.t.add[1]
}

/**
 * Opération : Déplacement de drone
 * Précondition : 
 */
pred deplacerDrone [t, t': Time, drone: Drone] 
{
	// Précondition
	//drone.commande.coordonnees != drone.coordonnees.t	

	// TODO : si commande on se dirige vers elle, sinon retour entrepot
	// On regarde si le receptacle cible change.
	drone.coordonnees.t = drone.receptacleCible.t.coordonnees => {
		// On ajoute le réceptacle au chemin parcouru
		one c: Chemin | c.receptaclesVisites = drone.cheminTraverse.t.receptaclesVisites + drone.receptacleCible.t && drone.cheminTraverse.t' = c
		// Le receptacle cible change
		some r: Receptacle | r.coordonnees.positionVoisin[drone.coordonnees.t] && r not in drone.cheminTraverse.t'.receptaclesVisites && drone.receptacleCible.t' = r
	} else {
		// On garde le même réceptacle cible
		drone.receptacleCible.t' = drone.receptacleCible.t
		// On garde le même chemin
		drone.cheminTraverse.t' = drone.cheminTraverse.t
	}

	// On se dirige vers le receptacle cible a l'instant t'
	(
		(drone.receptacleCible.t'.coordonnees.x > drone.coordonnees.t.x && drone.coordonnees.t'.x = drone.coordonnees.t.x.add[1] && drone.coordonnees.t'.y = drone.coordonnees.t.y)
  	 || (drone.receptacleCible.t'.coordonnees.x < drone.coordonnees.t.x && drone.coordonnees.t'.x = drone.coordonnees.t.x.sub[1] && drone.coordonnees.t'.y = drone.coordonnees.t.y)
     || (drone.receptacleCible.t'.coordonnees.y > drone.coordonnees.t.y && drone.coordonnees.t'.y = drone.coordonnees.t.y.add[1] && drone.coordonnees.t'.x = drone.coordonnees.t.x)
     || (drone.receptacleCible.t'.coordonnees.y < drone.coordonnees.t.y && drone.coordonnees.t'.y = drone.coordonnees.t.y.sub[1] && drone.coordonnees.t'.x = drone.coordonnees.t.x)
	)

	// Diminution de la batterie
	drone.batterie.t' = drone.batterie.t.sub[1]
}	

/**
 * Opération : Livrer une commande
 * Précondition : Batterie non pleine (on vient d'arriver), ie < 3 && Sur les coordonnees de livraison
 */
pred livrer [t, t': Time, drone: Drone] 
{
	// Précondition
	drone.coordonnees.t = drone.commande.coordonneesLivraison && drone.batterie.t < 3

	// Nouvelles valeurs
	drone.coordonnees.t' = drone.coordonnees.t
	drone.receptacleCible.t' = drone.receptacleCible.t
	drone.cheminTraverse.t' = drone.cheminTraverse.t
	drone.batterie.t' = drone.batterie.t

	// TODO : Mettre commande à 0 -> commande doit dépendre du temps aussi !
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
	#Drone = 1		// DNB
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
	// all e0 : Entrepot | #e0.receptaclesVoisins > 1

	// Associe des receptacles voisins aux entrepots
	all e : Entrepot, r : Receptacle 
		| (r.coordonnees.positionVoisin[e.coordonnees] <=> r in e.receptaclesVoisinsEntrepot)

	// Empeche un receptacle d'etre son propre voisin
	all r0 : Receptacle 
		| !(r0 in r0.receptaclesVoisins)

	// Associe pour chaque receptacle ses receptacles voisins
	all r0 : Receptacle, r1 : r0.receptaclesVoisins 
		| r0.coordonnees.positionVoisin[r1.coordonnees] && r0 in r1.receptaclesVoisins

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

/********************************* Lancements *********************************/

/**
 * Predicat vide permettant la simulation
 */ 
pred go
{
}

run go for 10 but 1 Drone, 6 Receptacle, 5 Time, 1 Commande, 6 int

