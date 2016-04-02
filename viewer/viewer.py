import os, sys 
from PyQt4 import QtGui, QtCore
from PyQt4.QtCore import *
from PyQt4.QtGui import *
import xml.etree.ElementTree as etree

COLORS = {
    "BLACK" : QColor(0,0,0),
    "RED" : QColor(255,120,120),
    "GREY" : QColor(220,220,220),
    "DRONE" : QColor(25,120,200,150),
    "ENTREPOT" : QColor(200,40,25,120),
    "RECEPTACLE" : QColor(25,200,60,120)
}

SCALE = 10
DRONE_SCALE = 0.005

class Scene(QtGui.QGraphicsScene):
    def __init__(self, windowParam):
        QtGui.QGraphicsScene.__init__(self)
        self.mainWindow = windowParam
        self.droneMap = QtGui.QPixmap("ship.png")

    def fill(self):
        self.setSceneRect(-SCALE*2,-SCALE*2,SCALE*4,SCALE*4)

        #Ajout d'une grille en fond
        axis_x = self.addLine(-SCALE,0,SCALE,0,QtGui.QPen(COLORS["RED"]))
        axis_y = self.addLine(0,-SCALE,0,SCALE,QtGui.QPen(COLORS["RED"]))
        for i in range(-SCALE,SCALE):
            if(i!=0):
                self.addLine(-SCALE,i,SCALE,i,QtGui.QPen(COLORS["GREY"]))
                self.addLine(i,-SCALE,i,SCALE,QtGui.QPen(COLORS["GREY"]))

    def updateScene(self):
        items = self.items()
        for i in items:
            if not (isinstance(i, QGraphicsLineItem)):
                self.removeItem(i)

        for drone in self.mainWindow.drones[int(self.mainWindow.time_control.value())]:
            coords = self.mainWindow.coordinates[drone["ckey"]]
            d = self.addPixmap(self.droneMap)
            d.scale(DRONE_SCALE, DRONE_SCALE)
            d.setOffset(-self.droneMap.width()/2,-self.droneMap.height()/2)
            d.setPos(coords["x"], coords["y"])

        for r in self.mainWindow.receptacles:
            coords = self.mainWindow.coordinates[r["ckey"]]
            radius = 2.0
            el = self.addEllipse(0-radius/2, 0-radius/2, radius, radius, QtGui.QPen(COLORS["BLACK"]), QBrush(COLORS["RECEPTACLE"]))
            el.setPos(coords["x"], coords["y"])
            
        for e in self.mainWindow.entrepots:
            coords = self.mainWindow.coordinates[e["ckey"]]
            radius = 2.0
            el = self.addEllipse(0-radius/2, 0-radius/2, radius, radius, QtGui.QPen(COLORS["BLACK"]), QBrush(COLORS["ENTREPOT"]))
            el.setPos(coords["x"], coords["y"])

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
        self.receptacles = []
        self.entrepots = []

        #Place each object
        for t in tree.findall(".//field[@label='coordonnees']/tuple"):
            label = t[0].get("label")
            if(label.startswith("Drone")):
                self.drones[int(t[2].get("label")[5])].append({
                    'label' : label,
                    'ckey' : t[1].get("label")
                })
            elif(label.startswith("Receptacle")):
                self.receptacles.append({
                    'label' : label,
                    'ckey' : t[1].get("label")
                })
            elif(label.startswith("Entrepot")):
                self.entrepots.append({
                    'label' : label,
                    'ckey' : t[1].get("label")
                })

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
