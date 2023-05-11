var radius = 20;                                                 // vertex radius.
var container = document.getElementById("contentContainer");     // container for both canvas.
var canvas = document.getElementById('canvas');                  // flow network canvas.
var canvas2 = document.getElementById('canvas2');                // residual network canvas.
var context = canvas.getContext("2d");                           // flow network context.
var context2 = canvas2.getContext("2d");                         // residual network context.
var vertexMenu = document.getElementById("vertexMenu");          // vertex menu.
vertexMenu.style.display = 'none';
var edgeMenu = document.getElementById("edgeMenu");              // edge menu.
edgeMenu.style.display = 'none';
var mygraph = new graph();        // flow network database and functions.
var copyGraph, copyS, copyT;
var maxCapacity = 100;            // edges maximum capacity.

document.getElementById("maxCap").onchange = function () {          // sets new max capacity.
    var cap = parseInt(document.getElementById("maxCap").value);
    if (cap < 10)
        cap = 10;
    maxCapacity = cap;
}
/* canvas properties */
var offset = 10;                         // offset to draw edge from center.
var fontSize = 12;                      
context2.font = fontSize + "pt Times New Roman";
context.font = fontSize + "pt Times New Roman";

/* algorithm attributes */
var alg = 0;            //0-edmonds karp, 1-capacity scaling.
document.getElementById("algorithm").onchange = function () {           // sets algorithm type.
    if (document.getElementById("algorithm").value === "edmondsKarp")
        alg = 0;
    else alg = 1;
    mygraph.clearAlg();
}
var playing = false;
var delta;     // for capacity scaling algorithm.
var Cf;        // how much can we augment?
var maxFlow;   // the max flow.
var p;         // the augmenting path.
var source = -1;        // source id.
var sink = -1;          // sink id.
document.getElementById('restoreB').disabled = true;
var playB = document.getElementById('playButton');
var clrAlg = document.getElementById('clearAlg');
clrAlg.disabled = true;

/* animation */
var blink = null;
var interval;
var speed = 1;

/* Queue Class (FIFO) - used in BFS() and with blinking animation */
function Queue() {          
    this.arr = [];
    /* return true if Queue is empty, else return false */
    this.isEmpty = function () {
        if (this.arr.length === 0)
            return true;
        else return false;
    };
    /* add new element to head */
    this.enqueue = function (item) {
        this.arr.unshift(item);
    };
    /* remove and return the last element on the Queue */
    this.dequeue = function () {
        if (this.isEmpty === true)
            return null;
        else return this.arr.pop();
    };
    /* return last element in the queue */
    this.getHead = function () {
        if (this.isEmpty === true)
            return null;
        else return this.arr[this.arr.length - 1];
    };
    /* remove and return first element */
    this.popHead = function () {
        if (this.isEmpty === true)
            return null;
        else return this.arr.shift();
    };
}       // Queue Class



function Vertex(id, x, y, color) {                                      /* Vertex Class */
    /// <summary>create a new Vertex</summary>   
    this.id = id;     
    this.x = x;
    this.y = y;
    if (color === null)
        this.color = "white";
    else this.color = color;

    //attributes for algorithms
    this.neighbors = [];            // adjacency list for the residual network.
    this.prev = -1; 			// previous vertex.
    this.flag = 0;      // indicates wheter a node is treated or not. (color white,red,black).
    this.dist = -1; 				// distance from S.

    this.setPosition = function (x, y) {
        /// <summary>sets Vertex's new position</summary>  
        this.x = x;
        this.y = y;
        this.draw();
    };
    /* draws a Vertex */
    this.draw = function () {
        context.beginPath();
        context2.beginPath();
        context.arc(this.x, this.y, radius, 0, 2 * Math.PI, false);
        context2.arc(this.x, this.y, radius, 0, 2 * Math.PI, false);
        context.fillStyle = this.color;
        context2.fillStyle = this.color;
        context.fill();
        context2.fill();
        context.lineWidth = 1;
        context2.lineWidth = 1;
        context.strokeStyle = '#003300';
        context2.strokeStyle = '#003300';
        context.stroke();
        context2.stroke();
        context.closePath();
        context2.closePath();
        if (this.color === "white"){
            context.fillStyle = 'black';
            context2.fillStyle = 'black';
        }
        else{
            context.fillStyle = 'white';
            context2.fillStyle = 'white';
        }            
        context.save();
        context2.save();
        context.textBaseline = 'middle';
        context2.textBaseline = 'middle';
        context.textAlign = 'center';
        context2.textAlign = 'center';      
        context.fillText(this.id, this.x, this.y);
        context2.fillText(this.id, this.x, this.y);
        context.restore();
        context2.restore();
    };
    /* copy a vertex without algorithm properties */
    this.copy = function () {
        return new Vertex(this.id, this.x, this.y, this.color);
    };
}       // Vertex Class
function ResidualEdge(u, v, c) {
    /// <summary>create a new Residual Edge (u,v)</summary>  
    this.u = u;         // from Vertex id
    this.v = v;         // to Vertex id
    this.c = c;         // capacity
    this.color = "darkgreen";
    this.reverseEdge = null;
    this.flag = false;
    /* Draw the residual edge in the residual network */
    this.draw = function () {
        var from = getCoords(u);
        var to = getCoords(v);
        // as vector from p1 to p2
        var nx = to.x - from.x;
        var ny = to.y - from.y;
        // get length
        const len = Math.sqrt(nx * nx + ny * ny);
        // use the length to normalise the vector
        nx /= len;
        ny /= len;
        context2.setTransform(
           nx, ny,   // the x axis
          -ny, nx,  // the y axis at 90 deg to the x axis
           from.x, from.y  // the origin (0,0)
        )
        context.lineWidth = 2;
        context2.lineWidth = 2;
        context2.fillStyle = this.color;
        context2.strokeStyle = this.color;
        if (this.reverseEdge.c === 0 || this.c === 0) {
            var c = this.c;
            if (this.c === 0) {
                c = this.reverseEdge.c;
                context2.fillStyle = 'brown';
                context2.strokeStyle = 'brown';
            }
            context2.beginPath();
            context2.lineTo(0, 0);  // start of line
            context2.lineTo(len, 0); // end of line
            context2.stroke();
            // add the arrow head
            if (this.c === 0) {
                context2.beginPath();
                context2.lineTo(radius, 0); // tip of arrow
                context2.lineTo(radius + 10, 5);
                context2.lineTo(radius + 10, -5);
                context2.fill();
            }
            else {
                context2.beginPath();
                context2.lineTo(len - radius, 0); // tip of arrow
                context2.lineTo(len - 10 - radius, 5);
                context2.lineTo(len - 10 - radius, -5);
                context2.fill();
            }
            context2.save();
            context2.textBaseline = 'bottom';
            context2.textAlign = 'center';
            if (this.flag === false)
                context2.fillText(c, len / 2, -2);
            else 
                context2.fillText("+" + Cf, len / 2, -2);
            context2.restore();
        }
        else 
        {
            context2.beginPath();
            context2.lineTo(0, offset); // start of line
            context2.lineTo(len, offset); // end of line
            context2.stroke();
            var tip = Math.sqrt(radius * radius - offset * offset);
            // add the arrow head
            context2.beginPath();
            context2.lineTo(len - tip, offset); // tip of arrow
            context2.lineTo(len - 10 - radius, offset + 5);
            context2.lineTo(len - 10 - radius, offset - 5);
            context2.fill();

            context2.beginPath();
            context2.fillStyle = 'brown';
            context2.strokeStyle = 'brown';
            context2.moveTo(0, -offset); // start of second line
            context2.lineTo(len, -offset); // end of second line
            context2.stroke();

            // add second  arrow head
            context2.beginPath();
            context2.lineTo(tip, -offset); // tip of arrow
            context2.lineTo(10 + radius, -offset + 5);
            context2.lineTo(10 + radius, -offset - 5);
            context2.fill();

            // text
            context2.save();
            context2.textBaseline = 'bottom';
            context2.fillStyle = 'darkgreen';
            context2.textAlign = 'center';
            if (this.flag === false)
                context2.fillText(this.c, len / 2, offset + 20);
            else context2.fillText("+" + Cf, len / 2, offset + 20);
            context2.fillStyle = 'brown';
            context2.fillText(this.reverseEdge.c, len / 2, -offset - 2);
            context2.restore();
        }
        context2.setTransform(1, 0, 0, 1, 0, 0);  // restore default transform
    };      // draw
}       // ResidualEdge

function Edge(u, v, c) {                        /* Edge Class */
    /// <summary>create a new Edge (u,v)</summary>  
    this.u = u;         // from Vertex id
    this.v = v;         // to Vertex id
    this.c = c;         // capacity
    this.f = 0;         // flow
    this.color = "black";
    this.residualEdge = -1;   // residual edge index.
    this.flag = false;      // indicates what to draw.

    /* Draws edge */
    this.draw = function () {
       mygraph.residual[this.residualEdge].draw();       // draw Edge in residual network.
        var from = getCoords(this.u);
        var to = getCoords(this.v);
        // as vector from p1 to p2
        var dx = to.x - from.x;
        var dy = to.y - from.y;
        // get length
        const len = Math.sqrt(dx * dx + dy * dy);
        // use the length to normalise the vector
        dx /= len;
        dy /= len;
        context.setTransform(
           dx, dy,   // the x axis
          -dy, dx,  // the y axis at 90 deg to the x axis
           from.x, from.y  // the origin (0,0)
        )

        context.fillStyle = this.color;
        context.strokeStyle = this.color;
        context.lineWidth = 2;
        context2.lineWidth = 2;
        context.beginPath();
        context.lineTo(0, 0);  // start of line
        context.lineTo(len, 0); // end of line
        context.stroke();

        // add the arrow head
        context.beginPath();
        context.lineTo(len - radius, 0); // tip of arrow
        context.lineTo(len - 10 - radius, 5);
        context.lineTo(len - 10 - radius, -5);
        context.fill();

        /* draw text */
        context.save();
        context.textBaseline = 'bottom';
        context.textAlign = 'center';
        var txt;
        if (this.flag === false) {
            context.fillStyle = 'blue';
            txt = this.c;
            if (this.f > 0)
                txt = this.f + " / " + txt;
        }
        else {
            context.fillStyle = 'red';
            txt = "+" + Cf;
        }
        context.fillText(txt, len / 2, -2);
        context.restore();
        context.setTransform(1, 0, 0, 1, 0, 0);  // restore default transform
    }; // draw()
    /* copy an edge without algorithm peoperties */
    this.copy = function () {
        return new Edge(this.u, this.v, this.c);
    };
}       // Edge Class

/* Graph data structure and fucntions */
function graph() {
    this.vertices = [];
    this.edges = [];
    this.n = 0;              // vertices count (for id)
    this.residual = [];     // representing edges in the residual network
    /* if graph contains no vertices, return true. else, return false. */
    this.isEmpty = function () {
        if (this.vertices.length === 0)
            return true;
        return false;
    };

    this.addVertex = function (x, y, color) {
        /// <summary>add a new Vertex</summary>  
        this.n++;
        this.vertices.push(new Vertex(this.n, x, y, color));
        this.clearAlg();
    };
    this.addEdge = function (u, v, c) {
        /// <summary>add a new Edge (u,v) </summary>
        if (u === v || c===0) return;
        if (this.existsEdge(u, v) || this.existsEdge(v, u)) return;      // if edge exist, do nothing.
        var edge = new Edge(u, v, c);
        /* update residual network */
        var residualEdge = new ResidualEdge(u, v, c);
        var reverseEdge = new ResidualEdge(v, u, 0);
        residualEdge.reverseEdge = reverseEdge;
        reverseEdge.reverseEdge = residualEdge;
        this.residual.push(residualEdge);
        edge.residualEdge = this.residual.length - 1;
        this.edges.push(edge);
        /* register neighbors (residual network) */
        this.vertices[this.getIndex(u)].neighbors.push(this.vertices[this.getIndex(v)]);
        this.clearAlg();
    };
    this.existsEdge = function (u, v) {
        /// <summary>check if edge exist</summary>  
        for (var i = 0; i < this.edges.length; i++) {
            if ((u === this.edges[i].u && v === this.edges[i].v)) {
                return true;
            }
        }
        return false;
    };

    this.deleteVertex = function (id) {
        /// <summary>Delete a Vertex</summary>  
        /// <param name='id' type="Number">Vertex id</param> 
        var i = this.getIndex(id);
        if (i !== -1)        // if vertex exist, remove it.
            this.vertices.splice(i, 1);
        for (i = this.edges.length - 1; i >= 0; i--) {      // remove all edges associated with the vertex.
            if (this.edges[i].u === id || this.edges[i].v === id)
                this.edges.splice(i, 1);
        }
        /* remove from neighbors lists */
        var j, n;
        for (i = 0; i < this.vertices.length; i++) {
            n = this.vertices[i].neighbors;
            for (j = n.length - 1; j >= 0; j--)
                if (id === n[j].id) {
                   n.splice(j, 1);
                    continue;
                }
        }
        this.clearAlg();
    };

    this.deleteEdge = function (index) {
        /// <summary>Delete an Edge</summary>  
        if (index !== -1) {        // if edge exist
            /* remove from residual edges */
            this.residual.splice(this.edges[index].residualEdge, 1);
            /*update indexe*/
            var i = this.edges[index].residualEdge;
            for (; i < this.edges.length; i++)
                this.edges[i].residualEdge--;
            /* remove from neighbors lists */
            var v = this.edges[index].v;
            i = this.getIndex(this.edges[index].u);
            for (j = 0; j < this.vertices[i].neighbors.length; j++) {
                if (v === this.vertices[i].neighbors[j].id) {
                    this.vertices[i].neighbors.splice(j, 1);
                    break;
                }
            }
            this.edges.splice(index, 1);
            this.clearAlg();
        }
    };
    /* Delete all Vertices and Edges */
    this.reset = function () {
        /* reset configuration */
        clearInterval(interval);
        playing = false;
        maxFlow = 0;
        Cf = 0;
        document.getElementById("MaxFlowText").value = maxFlow;
        document.getElementById("aug").value = 0;
        document.getElementById("path").value = 0;
        sink = -1;
        source = -1;
        var i;
        for (i = this.vertices.length; i > 0; i--) {        // reset vertices.
            this.vertices.pop();
        }
        this.n = 0;
        for (i = this.edges.length; i > 0; i--) {           // reset edges.
            this.edges.pop();
        }
        for (i = this.residual.length; i > 0; i--) {        // reset residual edges.
            this.residual.pop();
        }
        playB.disabled = false;
        document.getElementById('saveB').disabled = false;
        clrAlg.disabled = true;
        this.clearCanvas();
        this.draw();
    };
    /* clear algorithm data, the graph stays the same */
    this.clearAlg = function () {
        clearInterval(interval);
        maxFlow = 0;
        Cf = 0;
        delta = 0;
        document.getElementById("MaxFlowText").value = maxFlow;
        document.getElementById("aug").value = 0;
        document.getElementById("path").value = 0;
        playing = false;
        var edge, n, j, flag, i;
        for (i = 0; i < this.edges.length; i++) {
            edge = this.edges[i];
            edge.f = 0;
            edge.flag = false;
            edge.color = 'black';
            this.residual[edge.residualEdge].flag = false;
            this.residual[edge.residualEdge].color = 'darkgreen';
            this.residual[edge.residualEdge].c = edge.c;
            this.residual[edge.residualEdge].reverseEdge.c = 0;

            // re-register neighbors (residual network) 
            if (edge.c > 0){
                n = this.vertices[this.getIndex(edge.u)].neighbors;
                flag = false;
                for (j = 0; j < n.length; j++) {
                    if (n[j].id === edge.v)
                        flag = true;
                }
                if (flag === false)
                    n.push(this.vertices[this.getIndex(edge.v)]);
            }
        }
    
        for (i = 0; i < this.vertices.length; i++) {
            this.vertices[i].prev = -1;
            this.vertices[i].flag = 0;
            this.vertices[i].dist = -1;
        }
        if (p !== null && p !== undefined)
            p.splice(0, p.length);
        else p = [];
            
        playB.disabled = false;
        document.getElementById('saveB').disabled = false;
        clrAlg.disabled = true;
        this.clearCanvas();
        this.draw();
    };
    /* Draw the graph */
    this.draw = function () {
        var i;
        for (i = 0; i < this.edges.length; i++) {
            this.edges[i].draw();
        }
        for (i = 0; i < this.vertices.length; i++) {
            this.vertices[i].draw();
        }
    };

    /* resets the canvas */
    this.clearCanvas = function() {
        context.clearRect(0, 0, canvas.width, canvas.height);
        context2.clearRect(0, 0, canvas2.width, canvas2.height);
    };
    this.getIndex = function (id) {        
        /// <summary>get Vertex index in vertices array</summary>  
        for(var i=0; i<this.vertices.length; i++){
            if (this.vertices[i].id === id){
                return i;
            }
        }
        return -1;
    };

    this.getEdge = function (u, v) {
        /// <summary>get Edge index</summary>  
        var i;
        for (i = 0; i < this.edges.length; i++) {
            if (this.edges[i].u === u && this.edges[i].v === v)
                return i;
        }
        return -1;
    };

    this.updateResidual = function (f, c, index) {
        /// <summary>update residual network</summary>
        if (c === f) {      // remove from neighbors
            var n = this.vertices[this.getIndex(this.edges[index].u)].neighbors;
            var i;
            for (i = 0; i < n.length; i++) {
                if (n[i].id === this.edges[index].v) {
                    n.splice(i, 1);
                    break;
                }
            }
        }
        var edge = this.edges[index].residualEdge;
        if (edge !== -1) {
            this.residual[edge].c = c - f;
            this.residual[edge].reverseEdge.c = f;
        }
        this.clearCanvas();
        this.draw();
    };
    /* copy the entire graph without algorithm properties */
    this.copy = function () {
        var newGraph = new graph();
        var i, residualEdge, reverseEdge, e;
        /* copy vertices */
        for (i = 0; i < this.vertices.length; i++)
            newGraph.vertices.push(this.vertices[i].copy());
        newGraph.n = this.n;
        /* copy edges and residual edges */
        for (i = 0; i < this.edges.length; i++) {
            e = this.edges[i].copy();
            residualEdge = new ResidualEdge(e.u, e.v, e.c);
            reverseEdge = new ResidualEdge(e.v, e.u, 0);
            residualEdge.reverseEdge = reverseEdge;
            reverseEdge.reverseEdge = residualEdge;
            newGraph.residual.push(residualEdge);
            e.residualEdge = newGraph.residual.length - 1;
            newGraph.edges.push(e);
        }
        /* register neighbors */
        newGraph.clearAlg();
        return newGraph;
    };
}   // Graph class
/*************************** general functions *************************************/
function getCoords(id) {
    /// <summary>get Vertex coordinates</summary>  
    var i = mygraph.getIndex(id);
    if (i != -1) { return { x: mygraph.vertices[i].x, y: mygraph.vertices[i].y }; }
    else return null;
};
/* save the current graph */
function save() {
    copyGraph = mygraph.copy();
    copyS = source;
    copyT = sink;
    document.getElementById('restoreB').disabled = false;
}
/* restore last saved graph */
function restore() {
    mygraph.reset();
    mygraph = copyGraph;
    source = copyS;
    sink = copyT;
    mygraph.draw();
    document.getElementById('restoreB').disabled = true;
}

/* Show Vertex Menu in position (x,y) */
function showVertexMenu(x, y) {
    showingVertexMenu = true;
    if (playing === true)
        disableCriticalButtons();
    else enableCriticalButtons();
    vertexMenu.style.display = 'block';
    vertexMenu.style.position = 'absolute';
    vertexMenu.style.left = x + Math.round(vertexMenu.offsetWidth / 2) + 'px';
    vertexMenu.style.top = y + Math.round(vertexMenu.offsetHeight / 2) + 'px';
}
/* Show Edge Menu in position (x,y) */
function showEdgeMenu(x, y) {
    showingEdgeMenu = true;
    var e = mygraph.edges[hitEdge];
    if (playing === true)
        disableCriticalButtons();
    else enableCriticalButtons();
    if (e.u === source || e.u === sink || e.v === source || e.v === sink)
        document.getElementById("eButton1").disabled = true;
    else document.getElementById("eButton1").disabled = false;
    edgeMenu.style.display = 'block';
    edgeMenu.style.position = 'absolute';
    edgeMenu.style.left = x + 'px';
    edgeMenu.style.top = y + Math.round(edgeMenu.offsetHeight) + 'px';
}

/*disable algorithm - changing buttons */
function disableCriticalButtons() {
    document.getElementById("vButton2").disabled = true;
    document.getElementById("vButton3").disabled = true;
    document.getElementById("vButton4").disabled = true;
    document.getElementById("eButton1").disabled = true;
    document.getElementById("eButton2").disabled = true;
    document.getElementById("eButton3").disabled = true;
}

/*enable algorithm - changing buttons */
function enableCriticalButtons() {
    document.getElementById("vButton2").disabled = false;
    document.getElementById("vButton3").disabled = false;
    document.getElementById("vButton4").disabled = false;
    document.getElementById("eButton1").disabled = false;
    document.getElementById("eButton2").disabled = false;
    document.getElementById("eButton3").disabled = false;
}
/*************************** algorithms *************************************/
/* BFS traverse and update distance from source */
function BFS() {
    var i;
    /* initialzie */
    for (i = 0; i < mygraph.vertices.length; i++) {
        mygraph.vertices[i].flag = 0;
        mygraph.vertices[i].dist = -1;
        mygraph.vertices[i].prev = null;
    }
    //initialize source
    var s = mygraph.getIndex(source); 		//index of source in vertices[]
    mygraph.vertices[s].flag = 1;
    mygraph.vertices[s].dist = 0;
    mygraph.vertices[s].prev = null;
    var Q = new Queue(); 	//BFS queue
    Q.enqueue(mygraph.vertices[s]); 		//Q <-{s}

    var j, u, v, n;
    while (Q.isEmpty() != true) {
        u = Q.getHead();
        i = mygraph.getIndex(u.id);
        n = mygraph.vertices[i].neighbors;

        for (j = 0; j < n.length; j++) {        // for each neighbor of vertex u (in the residual network).
            v = n[j];
            if (v.flag === 0) {  
                if (alg === 0) {        // build augmenting path as shortest path if edmonds karp selected.
                    v.flag = 1;
                    v.dist = u.dist + 1;
                    v.prev = u;
                    Q.enqueue(v);
                }
                else {      // build augmenting path with capacity > delta if capacity scaling alg selected.
                    var edge = mygraph.getEdge(u.id, v.id);
                    if (edge !== -1 && mygraph.edges[edge].c >= delta) {
                        v.flag = 1;
                        v.dist = u.dist + 1;
                        v.prev = u;
                        Q.enqueue(v);
                    }
                }
            }
        }
        u.flag = 2;
        Q.dequeue();
    }
}
function augmentPath(i, j) {
    /// <summary>find augmenting path using BFS </summary> 
    BFS();      // BFS travers the graph updating distance.
    var s = mygraph.vertices[mygraph.getIndex(i)];
    var t = mygraph.vertices[mygraph.getIndex(j)];
    if (s === t) {
        return null;
    }
    blink = new Queue();
    p = [];
    var v = t;
    var edge;
    while (v !== s) {
        if (v === null || v.prev === null)     
            return null;
        edge = mygraph.getEdge(v.prev.id, v.id);    // edge index
        blink.enqueue(edge);
        p.unshift(v.id);
        v = v.prev;
    }
    p.unshift(s.id);
    return p;
}
/* run the algorithm and play the animation */
function play() {
    if (mygraph.vertices.length < 2) {
        alert("Must have at least 2 vertices.");
        return 0;
    }
    if (source === sink || source === -1 || sink === -1) {
        alert("Please choose a source and a sink.");
        return;
    }
    playing = true;
    /* initialize f=0 */
    var i, j;
    for (i = 0; i < mygraph.edges.length; i++) {
        mygraph.edges[i].f = 0;
        mygraph.updateResidual(0, mygraph.edges[i].c, i);
    }
    mygraph.draw();
    if (alg === 0) {        // Edmonds-Karp algorithm
        p = augmentPath(source, sink);
        if (p === null) {
            alert("There is no path between Vertex " + source + " and Vertex " + sink + ".");
            playing = false;
            return;
        }

    }
    else {              // capacity scaling algorithm
        delta = 0;      // initialzie delta
        var i;
        for (i = 0; i < mygraph.edges.length; i++) {
            if (source === mygraph.edges[i].u && mygraph.edges[i].c > delta)
                delta = mygraph.edges[i].c;
        }
        var two = 2;
        while (delta > two)
            two = two * 2;
        delta = two / 2;        // delta = highest power of 2 < C
        p = augmentPath(source, sink);
        if (delta < 1) {
            document.getElementById("MaxFlowText").value = maxFlow;
            document.getElementById("aug").value = 0;
            mygraph.clearCanvas();
            //mygraph.draw();
            playing = false;
            return;
        }
        while (p === null) {
            if (delta < 1) {
                document.getElementById("MaxFlowText").value = maxFlow;
                document.getElementById("aug").value = 0;
                mygraph.clearCanvas();
                mygraph.draw();
                playing = false;
                return;
            }
            p = augmentPath(source, sink);
            delta = delta / 2;
        }
    }
    playB.disabled = true;
    document.getElementById('saveB').disabled = true;
    maxFlow = 0;
    clrAlg.disabled = false;
    step();
}
/* make the augmenting path blink and add the flow using step() */
function augmentFlow() {
    var edge, i;
    maxFlow += Cf;
    document.getElementById("path").value++;
    blink = null;
    // redraw color black 
    for (i = 0; i < p.length - 1; i++) {
        edge = mygraph.getEdge(p[i], p[i + 1]);
        if (edge !== -1) {
            mygraph.edges[edge].color = "black";
            mygraph.residual[mygraph.edges[edge].residualEdge].color = "darkgreen";
        }
    }
    mygraph.clearCanvas();
    mygraph.draw();
    p = augmentPath(source, sink);
    if (alg === 0) {            // edmonds karp
        if (p === null) {
            document.getElementById("MaxFlowText").value = maxFlow;
            document.getElementById("aug").value = 0;
            playing = false;
        }
        else step();
    }
    else {      // capacity scaling
        if (delta < 1) {
            document.getElementById("MaxFlowText").value = maxFlow;
            document.getElementById("aug").value = 0;
            playing = false;
            return;
        }
        while (p === null) {
            if (delta < 1) {
                document.getElementById("MaxFlowText").value = maxFlow;
                document.getElementById("aug").value = 0;
                mygraph.clearCanvas();
                mygraph.draw();
                playing = false;
                return;
            }
            p = augmentPath(source, sink);
            delta = delta / 2;
        }
        step();
    }
}   // augmentFlow
/* make the augmenting path blink and add the flow */
function step() {
    var rIndex, edge, i;
    rIndex = mygraph.edges[mygraph.getEdge(p[0], p[1])].residualEdge;
    edge = mygraph.residual[rIndex];
    Cf = edge.c;
    /* find minimal flow to be added */
    for (i = 1; i < p.length - 1; i++) {
        rIndex = mygraph.edges[mygraph.getEdge(p[i], p[i + 1])].residualEdge;
        edge = mygraph.residual[rIndex];
        if (edge === -1) return 0;
        if (Cf > edge.c)
            Cf = edge.c;
    }
    var flag = false;
    var i = blink.popHead();
    var count = 0;
    document.getElementById("aug").value = Cf;  
    interval = setInterval(function () {            // every speed*10 miliseconds, the function will excecute.
        if (count > 10) {            // blink residual edge
            mygraph.edges[i].color = "red";
            if (flag === true) {
                mygraph.residual[mygraph.edges[i].residualEdge].color = "darkgreen";
                flag = false;
            }
            else {
                mygraph.residual[mygraph.edges[i].residualEdge].color = "red";
                flag = true;
            }
            mygraph.residual[mygraph.edges[i].residualEdge].flag = true;
        } else {
            if (flag === true) {                    // blink graph edge
                mygraph.edges[i].color = "black";
                flag = false;
            }
            else {
                mygraph.edges[i].color = "red";
                flag = true;
            }
        }
        mygraph.edges[i].flag = true;
        mygraph.clearCanvas();
        mygraph.draw();
        count++;
        if (count > 20) {
            count = 0;
            mygraph.edges[i].flag = false;
            mygraph.residual[mygraph.edges[i].residualEdge].flag = false;
            mygraph.edges[i].f += Cf;
            mygraph.edges[i].color = "red";
            mygraph.updateResidual(mygraph.edges[i].f, mygraph.edges[i].c, i);
            mygraph.clearCanvas();
            mygraph.draw();
            if (blink.isEmpty() === true) {
                clearInterval(interval);
                augmentFlow();
            }
            else {       
                i = blink.popHead();
            }        
        } 
    }, speed*10);       
}   
/**************** Sample Graphs ********************/
/* Generate a random flow network */
function randomGraph() {
    mygraph.reset();
    var graphs = [graphSample];  // array of build-graph functions
    var i = (Math.floor(Math.random() * 10)) % graphs.length;
    graphs[i]();
    mygraph.draw();
}
/* generate a random capacity edge */
function randomEdge(i, j) {
    var c = Math.round((Math.random() * maxCapacity)) % maxCapacity;
    if (i === source || i === sink || j === source || j === sink)
        mygraph.addEdge(i, j, c);
    else {
        var k = Math.random();
        if (k > 0.5)
            mygraph.addEdge(i, j, c);
        else mygraph.addEdge(j, i, c);   
    }
}
function graphSample() {                       // simple flow network
    mygraph.addVertex(80, 200, 'teal');
    mygraph.addVertex(230, 100, 'white');
    mygraph.addVertex(230, 300, 'white');
    mygraph.addVertex(380, 100, 'white');
    mygraph.addVertex(380, 300, 'white');
    mygraph.addVertex(530, 200, 'darkgrey');
    source = 1;
    sink = 6;
    randomEdge(1, 2);
    randomEdge(1, 3);
    randomEdge(2, 4);
    randomEdge(3, 2);
    randomEdge(3, 5);
    randomEdge(4, 3);
    randomEdge(4, 6);
    randomEdge(5, 4);
    randomEdge(5, 6);
}