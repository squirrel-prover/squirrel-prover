/***** Global parameters *****/

/**
 * Margin between nodes
 * @const
 * @type {number}
 */
const margin = 20
/**
 * Margin inside a node
 * @const
 * @type {number}
 */
const margin2 = 5





/***** Overview of the code *****/

/*** Overview of D3 ***/
// D3 use an object named "selection".
// A selection links a object with a DOM element.
// We will have two kind of selections :
// - one for nodes which represent timestamps
// - one for links which represent timestamp inequalities

/*** Nodes ***/
// A node, the object representing a timestamp, have this type:
// {
//   "id": String,
//   "name": String,
//   "cond": String (optional),
//   "state": String (optional),
//   "output": String (optional)
// }

// One the other hand, the associated DOM element has this structure: 
// <g class="node" id={String} transform="translate({Number}, {Number})">
//   <g class="line name" transform="translate({Number}, {Number})"> [...] </g>
//   <g class="line cond" transform="translate({Number}, {Number})"> [...] </g> (optional)
//   <g class="line state" transform="translate({Number}, {Number})"> [...] </g> (optional)
//   <g class="line output" transform="translate({Number}, {Number})"> [...] </g> (optional)
// </g>

// Each line is built like this:
// <g class="line {String}" transform="translate({Number}, {Number})">
//   <rect x="0" y="0" style="stroke: black; fill: none;" width="{Number}" height="{Number}"></rect>
//   <foreignObject width="{Number}" height="{Number}">
//     <div>
//       <span> {String} </span>
//     </div>
//   </foreignObject>
// </g>

/*** Links ***/
// The object representing a timestamp inequality is:
// {
//   "parent": node,
//   "child": node
// }

// The associated DOM element is a path:
// <path class="link" d="M {Number} {Number} C {Number} {Number}, {Number} {Number}, {Number} {Number}"></path>

/*** D3's joints ***/
// D3 
//

/***** Read file *****/

/**
 * @typedef {Object} Node
 * @property {string} id - Id of the node (unique)
 * @property {string} name - Name of the timestamp
 * @property {string} [cond] - Condition of the timestamp
 * @property {string} [state] - State modified at the timestamp
 * @property {string} [output] - Output of the timestamp
 */

/**
 * @typedef {Object} Node
 * @property {string} id - Id of the node (unique)
 * @property {string} name - Name of the timestamp
 * @property {string} [cond] - Condition of the timestamp
 * @property {string} [state] - State modified at the timestamp
 * @property {string} [output] - Output of the timestamp
 */


/** 
 * Send a request to read a JSON file.
 * If the request fails, return an object representing an empty graph.
 
 * @param {string} filePath - File's address 
 * @type {number}
 */
function loadJSONFile(filePath) {
  var result = null;
  var xmlhttp = new XMLHttpRequest();
  xmlhttp.open("GET", filePath, false);
  xmlhttp.send();
  if (xmlhttp.status==200) {
    result = JSON.parse(xmlhttp.responseText);
  } else {
    result = { "nodes": [], "layout": [] };
  }
  return result;
}

// [formatData(json)] takes the raw data obtains from the json file.
// Return an object containing two fields:
// - [layout] contains a list of list of nodes.
//   This structure represents the layout.
// - [links] is a list of pairs of nodes, one [parent] and a one [child]. */
function formatData(json) {
  // Create a mapping from id to the node designated by the id
  const map = {};
  json.nodes.forEach(node => {
    map[node.id] = node;
  });
  const result = new Object();
  result.nodes = json.layout.map((nodes,lineNumber) => {
    return nodes.map((layoutNode, columnNumber) => {
      const node = map[layoutNode.id];
      // We add a random to each node to help distinguish them
      node.color = Math.floor(Math.random() * 360);
      return node;
    });
  });
  result.links = [];
  json.nodes.forEach(node => {
    node.children.forEach(childId => {
      result.links.push({"parent": node, "child": map[childId]})
    });
  });
  return result;
}





/***** Layout *****/

function computeNodeSize(domNode) {
  var width = 0;
  var height = 0;
  d3.select(domNode)
    .selectAll(".line")
    .each((d,i,nodes) => {
      const domLine = nodes[i];
      const domSpan = d3.select(domLine).select("span").node();
      lineWidth = domSpan.offsetWidth + 2*margin2;
      lineHeight = domSpan.offsetHeight + 2*margin2;
      size.set(domLine, {"width": lineWidth, "height": lineHeight});
      width = Math.max(width, lineWidth);
      height += lineHeight;
    });
  size.set(domNode, {"width": width, "height": height});
}

function applyLineSize(domLine, nodeWidth, currentHeight, delay) {
  const selection = d3.select(domLine);
  const lineHeight = size.get(domLine).height;
  selection
    .transition().duration(delay)
    .attr("transform", d => `translate(0,${currentHeight})`);
  selection.select("rect")
    .transition().duration(delay)
    .attr("width", nodeWidth)
    .attr("height", lineHeight);
  selection.select("foreignObject")
    .transition().duration(delay)
    .attr("width", nodeWidth)
    .attr("height", lineHeight);
}

function applyNodeSize(domNode, delay) {
  const nodeWidth = size.get(domNode).width;
  var currentHeight = 0;
  d3.select(domNode)
    .selectAll(".line")
    .each((d,i,nodes) => {
      const domLine = nodes[i];
      applyLineSize(domLine, nodeWidth, currentHeight, delay);
      currentHeight += size.get(domLine).height;
    });
}

function computeAllPositions(data) {
  var maxX = margin;
  var x = margin;
  var y = margin;
  data.nodes.forEach(line => {
    var nextY = y + margin;
    line.forEach(node => {
      domNode = d3.select("#" + node.id).node();
      position.set(domNode, {"x": x, "y": y});
      x += margin + size.get(domNode).width;
      nextY = Math.max(nextY, y + margin + size.get(domNode).height);
    });
    maxX = Math.max(maxX, x);
    x = margin;
    y = nextY;
  });
  maxY = y;
  domSVG = d3.select("svg").node();
  size.set(domSVG, {"width": maxX, "height": maxY});
}

function applySVGPosition(delay) {
  // Resize svg window
  domSVG = d3.select("svg").node();
  sizeSVG = size.get(domSVG);
  d3.select("svg")
    .transition().duration(delay)
    .attr("width", sizeSVG.width)
    .attr("height", sizeSVG.height);
}

function applyNodePosition(selection, delay) {
  selection
    .transition().duration(delay)
    .attr("transform", (d,i,nodes) => {
      domNode = nodes[i];
      positionNode = position.get(domNode);
      return `translate(${positionNode.x},${positionNode.y})`;
    });
}

function applyLinkPosition(selection, delay) {
  selection
    .transition().duration(delay)
    .attr("d", d => {
      domParent = d3.select("#" + d.parent.id).node();
      domChild = d3.select("#" + d.child.id).node();
      const pX = position.get(domParent).x + (size.get(domParent).width/2);
      const pY = position.get(domParent).y + size.get(domParent).height;
      const cX = position.get(domChild).x + (size.get(domChild).width/2);
      const cY = position.get(domChild).y;
      return `M ${pX} ${pY} C ${pX} ${cY}, ${cX} ${pY}, ${cX} ${cY}`
    });
}

function applyAllPositions(selectionNodes, selectionLinks, delay) {
  applySVGPosition(delay);
  applyNodePosition(selectionNodes, delay);
  applyLinkPosition(selectionLinks, delay);
}





/***** Plot *****/

function enterLine(selection, kind, mutable, text, partialClick) {
  /* Create a new <g> for each nodes */
  /* If the datum has a property [kind],
     then we fill the newly created <g> with the expected information. */
  addLineSelection = selection.filter(d => d.hasOwnProperty(kind))
    .append("g")
      .classed("line", true)
      .classed(kind, true)
    .each((d,i,nodes) => {
      if (mutable) {
        expand.set(nodes[i], false);
      }
    });
  rectSelection = addLineSelection.append("rect")
    .attr("x", 0)
    .attr("y", 0)
    .style("stroke", "black")
    .style("fill", "none");
  if (!mutable) {
    rectSelection.style("fill", d => "hsl(" + d.color + ", 50%, 90%)");
  }
  ForeignSelection = addLineSelection.append("foreignObject")
  if (mutable) {
    ForeignSelection.on("click", function(d) {
      domLine = this.parentNode;
      span = d3.select(this).select("span");
      if (expand.get(domLine)) {
          span.html(text);
      } else {
        span.html(d[kind]);
      }
      expand.set(domLine, !expand.get(domLine));
      computeNodeSize(domLine.parentNode);
      applyNodeSize(domLine.parentNode, 200);
      computeAllPositions(data);
      applyAllPositions(d3.selectAll(".node"), d3.selectAll(".link"), 200);
      return;
    })
  }
  ForeignSelection.append("xhtml:div") //TODO Ajouter la marge dans le js
    .append("xhtml:span")
    .html(d => mutable ? text : d[kind]);
}

function enterNode(selection) {
  result = selection.append("g")
    .classed("node", true)
    .attr("id", d => d.id);
  partialClick = null;
  enterLine(result, "name", false);
  enterLine(result, "cond", true, "Condition", partialClick);
  enterLine(result, "state", true, "States", partialClick);
  enterLine(result, "output", true, "Output", partialClick);
  result.each((d,i,node) => {
    console.log(d);
    const domNode = node[i];
    computeNodeSize(domNode);
    applyNodeSize(domNode, 0);
  });
  return result;
}

function enterLink(selection) {
  return selection.append("path")
    .classed("link", true)
    .attr("stroke", d => "hsl(" + d.parent.color + ", 100%, 50%)")
    .attr("stroke-width", "2")
    .attr("fill", "none");
}

function updateNode(selection) {
  return selection
}

function updateLink(selection) {
  return selection
}

/* Create elements corresponding to the initial data in the svg */
function plot(svg, data) {
  selectionNodes = svg.selectAll("g.node")
    .data(data.nodes.flat(), d => d.id)
    .join(
      enter => enterNode(enter),
      update => updateNode(update),
      exit => exit.remove()
    );

  selectionLinks = svg.selectAll("path")
    .data(data.links, d => d.parent.id + d.child.id)
    .join(
      enter => enterLink(enter),
      update => updateLink(update),
      exit => exit.remove()
    );

  svgSize = computeAllPositions(data);
  applySVGPosition(0);
  applyAllPositions(selectionNodes, selectionLinks, 0);
}




/***** Execution *****/

/**/
var size = d3.local();
var position = d3.local();
var expand = d3.local();
/* Declare the main svg */
d3.select("body")
  .append("xhtml:div");
var svg = d3.select("body")
  .append("svg")
  .style('border', 'solid')
var svgWidth;
var svgHeight;

/* Initialisation */
var json = loadJSONFile("http://localhost:8080/dump.json");
d3.select("div")
  .html(json.layout.flat().map(x => x.id).toString());
var data = formatData(json);

plot(svg, data);

/* Events */
const es = new EventSource('events');
es.addEventListener('update',
  function(event){
    json = loadJSONFile("http://localhost:8080/dump.json");
    var text = json.layout.flat().map(x => x.id).toString();
    d3.select("div")
      .html(text ? text : "No data");
    data = formatData(json);
    plot(svg, data);
  });
