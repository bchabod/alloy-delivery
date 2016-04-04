import os, sys 
from PyQt4 import QtGui, QtCore
from PyQt4.QtCore import *
from PyQt4.QtGui import *
import xml.etree.ElementTree as etree

COLORS = {
    "BLACK" : QColor(0,0,0),
    "RED" : QColor(255,120,120),
    "GREY" : QColor(220,220,220),
    "DARKGREY" : QColor(150,150,150),
    "ENTREPOT" : QColor(200,40,25,140),
    "RECEPTACLE" : QColor(25,200,60,140),
    "COMMANDE" : QColor(255,255,102),
    "MULTIDRONE" : QColor(107,218,255)
}

SCALE = 10
DRONE_SCALE = 0.002

delta_pos = [
    [-1, 0],
    [0, -1],
    [1,  0],
    [0,  1],
    [-1,-1],
    [1, -1],
    [1,  1],
    [-1, 1]
]

class Scene(QtGui.QGraphicsScene):
    def __init__(self, windowParam):
        QtGui.QGraphicsScene.__init__(self)
        self.mainWindow = windowParam
        self.droneMap = QtGui.QPixmap("ship.png")
        self.batteryMap = [QtGui.QPixmap("level0.png"),QtGui.QPixmap("level1.png"),QtGui.QPixmap("level2.png"),QtGui.QPixmap("level3.png")]

    def fill(self):
        self.setSceneRect(-SCALE*2,-SCALE*2,SCALE*4,SCALE*4)

        self.gridGroup = QGraphicsItemGroup()
        #Ajout d'une grille en fond
        axis_x = self.addLine(-SCALE,0,SCALE,0,QtGui.QPen(COLORS["RED"]))
        axis_x.setGroup(self.gridGroup)
        axis_y = self.addLine(0,-SCALE,0,SCALE,QtGui.QPen(COLORS["RED"]))
        axis_y.setGroup(self.gridGroup)
        for i in range(-SCALE,SCALE):
            if(i!=0):
                l = self.addLine(-SCALE,i,SCALE,i,QtGui.QPen(COLORS["GREY"]))
                l.setGroup(self.gridGroup)
                l = self.addLine(i,-SCALE,i,SCALE,QtGui.QPen(COLORS["GREY"]))
                l.setGroup(self.gridGroup)
        self.addItem(self.gridGroup)

    def findSpot(self, coords, nbLines):
        spot = QPointF(coords["x"], coords["y"])
        rect = QRectF()
        line = QLineF()
        for far in range(2,5):
            foundFreeSpot = False
            for delta in delta_pos:
                newcoords = {
                    "x" : coords["x"] + delta[0]*far,
                    "y" : coords["y"] + delta[1]*far
                }
                rect = QRectF(QPointF(0,0), QPointF(1, 0.5 * nbLines))
                rect.moveCenter(QPointF(newcoords["x"], newcoords["y"]))
                line = QLineF(coords["x"], coords["y"], rect.center().x(), rect.center().y())
                foundFreeSpot = True
                items = self.items()
                for i in items:
                    r2 = i.sceneBoundingRect()
                    if(r2.contains(spot) or isinstance(i, QGraphicsLineItem)):
                        continue
                    if (not (isinstance(i, QGraphicsItemGroup)) and ( (rect.intersects(r2)) or ( \
                    line.intersect(QLineF(r2.topRight(), r2.topLeft()), QPointF())==QLineF.BoundedIntersection or \
                    line.intersect(QLineF(r2.topRight(), r2.bottomRight()), QPointF())==QLineF.BoundedIntersection or \
                    line.intersect(QLineF(r2.bottomLeft(), r2.topLeft()), QPointF())==QLineF.BoundedIntersection or \
                    line.intersect(QLineF(r2.bottomRight(), r2.bottomLeft()), QPointF())==QLineF.BoundedIntersection ))):
                        foundFreeSpot = False
                        break
                if(foundFreeSpot):
                    break
            if(foundFreeSpot):
                break
        if not foundFreeSpot:
            print("WARNING: could not place a label, dirty spot will be used")
        return {
            "rect" : rect,
            "line" : line
        }

    def updateScene(self):
        items = self.items()
        radius = 1.0

        for i in items:
            if not (isinstance(i, QGraphicsItemGroup) or (isinstance(i, QGraphicsLineItem) and i.group() == self.gridGroup)):
                self.removeItem(i)

        for r in self.mainWindow.receptacles[int(self.mainWindow.time_control.value())]:
            coords = self.mainWindow.coordinates[r["ckey"]]
            color = QBrush(COLORS["RECEPTACLE"]) if r["label"].startswith("Receptacle") else QBrush(COLORS["ENTREPOT"])
            el = self.addEllipse(0-radius/2, 0-radius/2, radius, radius, QtGui.QPen(COLORS["BLACK"]), color)
            el.setPos(coords["x"], coords["y"])
            font = QtGui.QFont("Georgia", 10);
            label = self.addText(r["label"].replace("Receptacle", "R").replace("Entrepot", "E"), font)
            label.scale(0.02, 0.02)
            label.setPos(coords["x"] - label.sceneBoundingRect().width()/2, coords["y"]- label.sceneBoundingRect().height()/2)

            #Add receptacle content
            if(r["label"].startswith("Receptacle")):
                rect = QRectF(QPointF(0,0), QPointF(0.25, 0.25))
                rect.moveCenter(QPointF(coords["x"] + radius/4, coords["y"] - radius/4))
                self.addRect(rect, QtGui.QPen(COLORS["BLACK"]), QBrush(COLORS["COMMANDE"]))
                font = QtGui.QFont("Georgia", 10);
                label = self.addText(r["contenance"], font)
                label.scale(0.01, 0.01)
                label.setPos(rect.center().x() - label.sceneBoundingRect().width()/2, 
                    rect.top() + (0.1) - label.sceneBoundingRect().height()/2)

        for ckey, d in self.mainWindow.commandes.items():
            coords = self.mainWindow.coordinates[ckey]
            nbLines = len(d)
            freeSpot = self.findSpot(coords, nbLines)
            l = self.addLine(freeSpot["line"], QtGui.QPen(COLORS["BLACK"]))
            r = self.addRect(freeSpot["rect"], QtGui.QPen(COLORS["BLACK"]), QBrush(COLORS["COMMANDE"]))
            font = QtGui.QFont("Georgia", 10);
            for index in range(0, len(d)):
                if(d[index]["done"] <= int(self.mainWindow.time_control.value())):
                    font.setStrikeOut(True)
                else:
                    font.setStrikeOut(False)
                label = self.addText(d[index]["label"].replace("Commande", "c") + " : " + d[index]["demande"], font)
                label.scale(0.015, 0.015)
                label.setPos(freeSpot["rect"].center().x() - label.sceneBoundingRect().width()/2, 
                    freeSpot["rect"].top() + (0.5*index + 0.25) - label.sceneBoundingRect().height()/2)
                if(d[index]["done"] <= int(self.mainWindow.time_control.value())):
                    label.setDefaultTextColor(COLORS["DARKGREY"])

        for drone in self.mainWindow.drones[int(self.mainWindow.time_control.value())]:
            coords = self.mainWindow.coordinates[drone["ckey"]]
            d = self.addPixmap(self.droneMap)
            d.scale(DRONE_SCALE, DRONE_SCALE)
            d.setOffset(-self.droneMap.width()/2,-self.droneMap.height()/2)
            d.setPos(coords["x"], coords["y"])

        for ckey, cobj in self.mainWindow.coordinates.items():
            counter = 0
            drones = []
            for drone in self.mainWindow.drones[int(self.mainWindow.time_control.value())]:
                if drone["ckey"]==ckey:
                    counter = counter + 1
                    drones.append(drone)

            #Add products labels
            if counter>=1:
                freeSpot = self.findSpot(cobj, len(drones))
                l = self.addLine(freeSpot["line"], QtGui.QPen(COLORS["BLACK"]))
                r = self.addRect(freeSpot["rect"], QtGui.QPen(COLORS["BLACK"]), QBrush(COLORS["MULTIDRONE"]))
                font = QtGui.QFont("Georgia", 10);
                for index in range(0, len(drones)):
                    label = self.addText(drones[index]["label"].replace("Drone", "d") + " : " + drones[index]["contenance"], font)
                    label.scale(0.015, 0.015)
                    label.setPos(freeSpot["rect"].center().x() - label.sceneBoundingRect().width()/2, 
                        freeSpot["rect"].top() + (0.5*index + 0.25) - label.sceneBoundingRect().height()/2)

            #Add drone counter of battery levels
            if counter>1:
                rect = QRectF(QPointF(0,0), QPointF(0.25, 0.25))
                rect.moveCenter(QPointF(cobj["x"] + radius/4, cobj["y"] - radius/4))
                self.addRect(rect, QtGui.QPen(COLORS["BLACK"]), QBrush(COLORS["MULTIDRONE"]))
                font = QtGui.QFont("Georgia", 10);
                label = self.addText("x" + str(counter), font)
                label.scale(0.01, 0.01)
                label.setPos(rect.center().x() - label.sceneBoundingRect().width()/2, 
                    rect.top() + (0.1) - label.sceneBoundingRect().height()/2)
            elif counter==1:
                b = self.addPixmap(self.batteryMap[drones[0]["battery"]])
                b.scale(DRONE_SCALE/2, DRONE_SCALE/2)
                b.setOffset(-self.batteryMap[drones[0]["battery"]].width()/2,-self.batteryMap[drones[0]["battery"]].height()/2)
                b.setPos(cobj["x"], cobj["y"])

class View(QtGui.QGraphicsView):
    def __init__(self):
        QtGui.QGraphicsView.__init__(self)

        self.setTransformationAnchor(QtGui.QGraphicsView.AnchorUnderMouse)
        self.setResizeAnchor(QtGui.QGraphicsView.AnchorViewCenter)
        self.setHorizontalScrollBarPolicy(QtCore.Qt.ScrollBarAlwaysOff)
        self.setVerticalScrollBarPolicy(QtCore.Qt.ScrollBarAlwaysOff)  
        self.setRenderHint(QtGui.QPainter.Antialiasing)

        self.setDragMode(QtGui.QGraphicsView.ScrollHandDrag)
        self.setRubberBandSelectionMode(QtCore.Qt.IntersectsItemShape)
   
    def wheelEvent(self, event):
        zoomInFactor = 1.25
        zoomOutFactor = 1 / zoomInFactor
        oldPos = self.mapToScene(event.pos())
        if event.delta() > 0:
            zoomFactor = zoomInFactor
        else:
            zoomFactor = zoomOutFactor
        self.scale(zoomFactor, zoomFactor)
        newPos = self.mapToScene(event.pos())
        delta = newPos - oldPos
        self.translate(delta.x(), delta.y())


class MainWindow(QtGui.QWidget):

    #Constructeur de la classe
    def __init__(self): 
        QtGui.QWidget.__init__(self) 

        #Mise en place de la fenetre
        self.setWindowTitle("Alloy Instance Viewer") 

        vbox = QtGui.QHBoxLayout()
        graphics = View()
        self.myscene = Scene(self)
        self.myscene.fill()
        graphics.setScene(self.myscene)
        graphics.fitInView(0,0,10/3,7.25/3)
        graphics.centerOn(0,0)
        vbox.addWidget(graphics)
        graphics.setFixedSize(800, 800)

        label_time = QLabel("Time step : ")
        self.time_control = spinBox(0,10,0,0,True,1)
        self.time_control.valueChanged.connect(self.myscene.updateScene)
        self.time_control.setDisabled(True)
        label_import = QLabel("Importer un fichier Alloy : ")
        self.open = QPushButton('Parcourir...', self)
        self.open.clicked.connect(self.handleOpen)

        controlLayout = QtGui.QVBoxLayout()
        controlLayout.addWidget(label_time)
        controlLayout.addWidget(self.time_control)
        spacer = QSpacerItem(20,40)
        controlLayout.addItem(spacer)
        controlLayout.addWidget(label_import)
        controlLayout.addWidget(self.open)
        controlLayout.setAlignment(Qt.AlignTop)

        vbox.addLayout(controlLayout)
        self.setLayout(vbox)
        self.center()
        graphics.scale(0.15, 0.15)

    def handleOpen(self):
        self.path = str(QFileDialog.getOpenFileName())
        tree = etree.parse(self.path)

        self.coordinates = {}

        #Retrieve coordinates keys
        for ckey in tree.findall(".//sig[@label='this/Coordonnees']/atom"):
            label = ckey.get("label")
            self.coordinates[label] = {
                'x' : 0,
                'y' : 0
            }

        #Fill the dictionnary
        for xtuple in tree.findall(".//field[@label='x']/tuple"):
            xkey = xtuple[0].get("label")
            xval = xtuple[1].get("label")
            self.coordinates[xkey]['x'] = int(xval)
        for ytuple in tree.findall(".//field[@label='y']/tuple"):
            ykey = ytuple[0].get("label")
            yval = ytuple[1].get("label")
            self.coordinates[ykey]['y'] = int(yval)

        #Get number of time steps
        nbSteps = len(tree.findall(".//sig[@label='this/Time']/atom"))
        self.time_control.setMaximum(nbSteps-1)
        self.time_control.setValue(0)
        self.drones = [[] for i in range(nbSteps)]
        self.receptacles = [[] for i in range(nbSteps)]
        self.commandes = {}

        #Place each object
        for t in tree.findall(".//field[@label='coordonnees']/tuple"):
            label = t[0].get("label")
            if(label.startswith("Drone")):

                #Find battery level for this timestamp
                bLevel = 3
                for b in tree.findall(".//field[@label='batterie']/tuple"):
                    if(b[0].get("label")==label and b[2].get("label")==t[2].get("label")):
                        bLevel = int(b[1].get("label"))

                #Check if there is a delivery goal at this timestamp
                #If there is one, try to get the goal number of products
                contenance = "0"
                cible = ""
                for d in tree.findall(".//field[@label='commande']/tuple"):
                    if(d[0].get("label")==label and d[2].get("label")==t[2].get("label")):
                        cible = d[1].get("label")
                        for dp in tree.findall(".//field[@label='poids']/tuple"):
                            if(dp[0].get("label") == cible):
                                contenance = dp[1].get("label")

                self.drones[int(t[2].get("label")[5:])].append({
                    'label' : label,
                    'ckey' : t[1].get("label"),
                    'battery' : bLevel,
                    'contenance' : contenance,
                    'cible' : cible
                })

            elif(label.startswith("Receptacle")):
                #Get receptacle weight timeline
                for nb in tree.findall(".//field[@label='contenanceActuelle']/tuple"):
                    if(nb[0].get("label") == label):
                        self.receptacles[int(nb[2].get("label")[5:])].append({
                            'label' : label,
                            'ckey' : t[1].get("label"),
                            'contenance' : nb[1].get("label")
                        })

            elif(label.startswith("Entrepot")):
                for step in range(0, nbSteps):
                    self.receptacles[step].append({
                        'label' : label,
                        'ckey' : t[1].get("label"),
                    })


        #Get deliveries
        for d in tree.findall(".//field[@label='coordonneesLivraison']/tuple"):
            label = d[0].get("label")

            #Find nbProducts needed for this delivery
            nbProducts = 3
            for nb in tree.findall(".//field[@label='poids']/tuple"):
                if(nb[0].get("label")==label):
                    nbProducts = nb[1].get("label")

            #Try to figure out when this delivery is fulfilled
            #Default value is nbSteps+1 = never
            doneTime = nbSteps+1
            for indexDrone in range(0, len(self.drones[0])):
                for time in range(0, nbSteps-1):
                    if (self.drones[time][indexDrone]["cible"] == label and \
                    self.drones[time+1][indexDrone]["cible"] == ""):
                        doneTime = time+1

            ckey = d[1].get("label")
            if ckey in self.commandes:
                self.commandes[ckey].append({
                    'label' : label,
                    'demande' : nbProducts,
                    'done' : doneTime
                })
            else:
                self.commandes[ckey] = [
                    {
                        'label' : label,
                        'demande' : nbProducts,
                        'done' : doneTime
                    }
                ]

        self.myscene.updateScene()
        self.time_control.setDisabled(False)

    def center(self):
        resolution = QtGui.QDesktopWidget().screenGeometry()
        self.move((resolution.width() / 2) - (self.frameSize().width() / 2),
                  (resolution.height() / 2) - (self.frameSize().height()))

def spinBox(mini=0,maxi=100,value=50,precision=0,buttons=False,step=1):
    spinbox = QDoubleSpinBox()
    spinbox.setRange(mini,maxi)
    spinbox.setDecimals(precision)
    spinbox.setValue(value)
    spinbox.setSingleStep(step)
    if not buttons:
        spinbox.setButtonSymbols(QAbstractSpinBox.NoButtons)
    return spinbox

def main():
    app = QtGui.QApplication([])
    frame = MainWindow() 
    frame.show() 
    app.exec_()

if __name__=='__main__':
    main()
