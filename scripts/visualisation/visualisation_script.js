/** Script used to read data sent by Squirrel and visualise them in a web browser.

  * <p><b>Data</b><br />
    Data sent by Squirrel must be in JSON format and fit the type Data or Error.
    </p>

  * <p><b>Structure of the code</b><br />
    Information on each element in the visualisation are stored in their own object (Node or Link).<br />
    These objects share some properties: `id` (used for data joins) and `selection`.
    Selections are object in D3 used to group elements of the DOM and pair them with data.
    We do not use them that way here: `selection` contains only one element.
    Using a selection and not directly the element allows us to use D3's readable syntax to modify attributes and styles of this element.
    Moreover `selection` is not paired with any data, since binding new data would erase the previous ones.
    To store data refering to an element, we use properties of the object and not the selection.<br />
    These objects' methods share the same nomenclature: When a property's value depends from another one and a method recomptute the first one in case the second one changed, this method is named `update`. When we modify the DOM element of `selection` to fit changes in the object's property, the method is named `refreshElement`.
    </p>
    
  * <p><b>D3's joins</b><br />
    To link data with DOM elements, we use D3's data joins.<br />
    D3 finds all elements of a certain class.
    On the other hand, it gets an array of data.
    To pair them, D3 needs a key: we use `id`.
    That is why all elements and data used for joins must have ids.<br />
    D3 will then create three selections: `enter` for data without element sharing the same id, `update` for element paired with a datum  and `exit` for elements without data.
    The methods `join` takes three functions as argument, each one describing what to do with these three selections.
    
    </p>
  
  * @file
  * @author Clément Hérouard
  */
/** Script used to read data sent by Squirrel and visualise them in a web browser.
  
  * Organisation of the code
  
  * Data
  
  * D3's joints
  
  * @file
  * @author Clément Hérouard
  */

/* -------------------------------------------------------------------------- */

/** D3's selection.
    @typedef {Object} Selection
  */

/** @typedef {Object} Data
  * @property {Array.<NodeDatum>} nodes - List of nodes
  * @property {Array.<Array.<string>>} layout - List of lists of identifiers.
    Represents the layout.
  */

/** Datum associated with a link
  * @typedef NodeDatum
  * @property {string} id - Identifier of the node. Unique for each node.
  * @property {string} name - Content for the line `name`.
  * @property {?string} cond - Content for the line `cond`.
  * @property {?string} state - Content for the line `state`.
  * @property {?string} output - Content for the line `output`.
  * @property {Array.<string>} children - List of identifiers of children of this node.
  */

/** Object describing an error in the data
  * @typedef Error
  * @property {string} error - Contains the error message
  */

/* -------------------------------------------------------------------------- */
    
/** Store variables common to all elements of the visualisation
  * @property {string} address - Address of the local server.
  * @property {number} margin - Margin between nodes.
  * @property {number} padding - Margin used inside nodes.
  * @property {number} lineBreakWidth - Maximum node width before a soft line break.
  * @property {number} clickDuration - Duration of the expansion induced by a click on a line.
  */
class Configuration {
  /** @param {string} address - Address of the local server.
    * @param {number} margin - Margin between nodes.
    * @param {number} padding - Margin used inside nodes.
    * @param {number} lineBreakWidth - Maximum node width before a soft line break.
    * @param {number} clickDuration - Duration of the expansion induced by a click on a line.
    */
  constructor(address, margin, padding, lineBreakWidth, clickDuration) {
    this.address = address;
    this.margin = margin;
    this.padding = padding;
    this.lineBreakWidth = lineBreakWidth;
    this.clickDuration = clickDuration;
  }
}

/* -------------------------------------------------------------------------- */

/** Read data on the local server.
  * @property {string} address - Address of the local server.
  */
class Reader {
  /** @param {string} address - Address of the local server.
    */
  constructor(address) {
    this.address = address;
  }
  
  /** Get the JSON data from the local server or an error object.
    * @type {Data | Error}
    */
  get data() {
    let result = null;
    let xmlhttp = new XMLHttpRequest();
    xmlhttp.open("GET", this.address, false);
    xmlhttp.send();
    if (xmlhttp.status==200) {
      result = JSON.parse(xmlhttp.responseText);
    } else {
      result = { "error": "Server not responding" };
    }
    return result;
  }
}

/* -------------------------------------------------------------------------- */

/** Contains information about a single node.
    This node represent a timestamp.
  * @property {string} kind - Identifier of the kind of information stored in the line
  * @property {string} text - Text to print in the line
  * @property {boolean} expandable - `true` if this line expands when clicked.
  * @property {?boolean} expanded - Describe if the line is expanded or not.
    (for expandable nodes)
  * @property {?string} shortText - Shorter version of the text.
    (for expandable nodes)
  * @property {?number} y - y-coordinate of the line.
    Relative to the node containing the line.
  * @property {number} ownWidth - Width required by the line to print its content.
  * @property {?number} width - Width of the line.
    Not defined by the constructor.
  * @property {number} height - Height of the line
  * @property {Selection} selection - Selection containing a single <g> element.
    Each element of the line are appended to this element.
  * @property {Scene} scene - Scene containing the node.
  */
class Line {
  /** Warning: This constructor does not define `y` and `width` properties.
    * @param {Selection} lineSelection - Selection containig a single <g> element.
    * @param {string} kind - Identifier of the kind of information stored in the line
    * @param {string} text - Text that will be printed on this line.
    * @param {Scene} scene - Scene containing the node.
    * @param {number} color - Number conding the color of the node.
      This number is a hue in HSL representation.
    * @param {boolean} expandable - `true` if this line expands when clicked.
    * @param {string} [shortText] - Short version of the text if the line is expandable.
    */
  constructor(lineSelection, kind, text, scene, color, expandable, shortText) {
    this.kind = kind;
    this.text = text;
    this.expandable = expandable;
    if (this.expandable) {
      this.expanded = false;
      this.shortText = shortText;
    }
    this.scene = scene;
    
    this.selection = lineSelection
      .classed("line", true)
      .classed(kind, true);
    this.selection.append("rect")
      .classed("line", true)
      .classed(kind, true)
      .attr("x", 0)
      .attr("y", 0)
      .style("stroke", "black")
      .style("stroke-width", 1)
      .style("fill", kind == "name" ? "hsl(" + color + ", 50%, 90%)" : "white");
    const foreignObjectSelection = this.selection.append("foreignObject")
      .classed("line", true)
      .classed(kind, true);
    foreignObjectSelection.append("xhtml:div")
      .classed("line", true)
      .classed(kind, true)
      .style("padding", this.scene.config.padding + "px")
      .append("xhtml:span")
      .classed("line", true)
      .classed(kind, true)
      .html(this.expandable ? this.shortText : this.text);
    if (expandable) {
      foreignObjectSelection.on("click", () => { this.expand() });
    }
    
    this.updateSize();
  }
  
  /** Set the property `y` of the line.
    * @param {number} y
    */
  setPosition(y) {
    this.y = y;
  }

  /** Set the properties `ownWidth` and `height` to fit the text printed inside the line.
    */
  updateSize() {
    const divSelection = this.selection.select("div")
      .style("width", this.scene.config.lineBreakWidth);
    const spanElement = this.selection.select("span").node();
    this.ownWidth = spanElement.offsetWidth + 1 + 2 * this.scene.config.padding;
    this.height = spanElement.offsetHeight + 2 * this.scene.config.padding;
    divSelection.style("width", `auto`);
  }

  /** Set the property `width` of the line.
    * @param {number} width
    */
  setWidth(width) {
    this.width = width;
  }

  /** Modify the DOM element corresponding to this line (stored in `selection`).
      Update of its position and size to fit `y`, `width` and `height`.
    * @param {number} duration - duration of the modification (in ms).
    */
  refreshElement(duration) {
    this.selection
      .transition().duration(duration)
      .attr("transform", `translate(0,${this.y})`);
    this.selection.select("rect")
      .transition().duration(duration)
      .attr("width", this.width)
      .attr("height", this.height);
    this.selection.select("foreignObject")
      .transition().duration(duration)
      .attr("width", this.width)
      .attr("height", this.height);
  }
  
  /** Swap the text inside the line between `text` and `shortText`.
      Toggle the value of `expanded`.
      Then, all objects' sizes and positions in the `scene` are computed anew.
      Elements are modified accordingly.
    */
  expand() {
    const spanSelection = this.selection.select("span");
    this.selection.select("span")
      .html(this.expanded ? this.shortText : this.text);
    this.expanded = !this.expanded;
    
    this.scene.updateAllSizesAndPositions();
    this.scene.refreshElement(this.scene.config.clickDuration);
  }
}

/* -------------------------------------------------------------------------- */

/** Contains information about a single node.
    This node represent a timestamp.
  * @property {string} id - Identifier of the node
  * @property {number} color - Number conding the color of the node.
    This number is a hue in HSL representation.
  * @property {?number} x - x-coordinate
  * @property {?number} y - y-coordinate
  * @property {?number} width - Width of the node
  * @property {?number} height - Height of the node
  * @property {Array.<Line>} lines - List of lines of the node.
    Lines are printed in the same order than this list.
  * @property {Selection} selection - Selection containing a single <g> element.
    Each element of the node are appended to this element.
  * @property {Scene} scene - Scene containing the node.
  */
class Node {
  /** Warning: This constructor does not define `y` and `width` properties.
    * @param {Selection} nodeSelection - Selection containig a single <g> element.
    * @param {NodeDatum} datum - Part of the data that the node will represent.
    * @param {Scene} scene - Scene containing the node.
    */
  constructor(nodeSelection, datum, scene) {
    this.id = datum.id;
    this.color = Math.floor(Math.random() * 360);
    this.scene = scene;
    
    this.selection = nodeSelection
      .classed("node", true)
      .attr("id", this.id);
    const nameLineSelection = this.selection.append("g");
    this.lines = [new Line(nameLineSelection, "name", datum.name, this.scene, this.color, false)];
    if ("cond" in datum) {
      const condLineSelection = this.selection.append("g");
      this.lines.push(new Line(condLineSelection, "cond", datum.cond, this.scene, this.color, true, "Condition"));
    }
    if ("state" in datum) {
      const stateLineSelection = this.selection.append("g");
      this.lines.push(new Line(stateLineSelection, "state", datum.state, this.scene, this.color, true, "States"));
    }
    if ("output" in datum) {
      const outputLineSelection = this.selection.append("g");
      this.lines.push(new Line(outputLineSelection, "output", datum.output, this.scene, this.color, true, "Output"));
    }
    this.selection.append("rect")
      .classed("node", true)
      .attr("x", 0)
      .attr("y", 0)
      .attr("stroke", "hsl(" + this.color + ", 100%, 50%)")
      .style("stroke-width", 2)
      .style("fill", "none");
    
    this.updateSize();
  }
  
  /** Set the property `y` in each line.
    */
  setLinesPosition() {
    let y = 0;
    this.lines.forEach(line => {
      line.setPosition(y);
      y += line.height;
    });
  }
  
  /** Set `x` and `y` properties
    * @param {number} x - x-coordinate
    * @param {number} y - y-coordinate
    */
  setPosition(x, y) {
    this.setLinesPosition();
    this.x = x;
    this.y = y;
  }

  /** Read properties in each line to set `width` and `height` of this node.
    * Then, set the `width` of each line to match the one of the node.
    */
  updateSize() {
    this.width = 0;
    this.height = 0;
    this.lines.forEach(line => {
      this.width = Math.max(line.ownWidth, this.width);
      this.height += line.height;
    });
    this.lines.forEach(line => {
      line.setWidth(this.width);
    });
  }

  /** Set the properties `width` and `height` in the nodes and its lines to fit the text in the node.
    */
  updateAllSizes() {
    this.lines.forEach(line => line.updateSize());
    this.updateSize();
  }
  
  /** Modify the DOM element corresponding to this node (stored in `selection`).
      Update its position and size to fit `x`, `y`, `width` and `height`.
      Also refresh each line in the node.
    * @param {number} duration - duration of the modification (in ms).
    */
  refreshElement(duration) {
    this.lines.forEach(line => line.refreshElement(duration));
    this.selection
      .transition().duration(duration)
      .attr("transform", `translate(${this.x},${this.y})`);
    this.selection.select("rect.node")
      .transition().duration(duration)
      .attr("width", this.width)
      .attr("height", this.height);
  }
  
  /** Get the coordinates of the endpoint of links having this node as child.
    * @type {{x: number, y: number}}
    */
  get childAnchor() {
    return {
      x: this.x + this.width / 2,
      y: this.y
    };
  }
  
  /** Get the coordinates of the endpoint of links having this node as parent.
    * @type {{x: number, y: number}}
    */
  get parentAnchor() {
    return {
      x: this.x + this.width / 2,
      y: this.y + this.height
    };
  }
}

/* -------------------------------------------------------------------------- */

/** Contains information about a single link between two nodes.
  * This link represent an inequality between two timestamps: tau1 <= tau2.
  * @property {string} id - Identifier of the link.
  * @property {Node} parent - Endpoint of the link. This node represents the first timestamp tau1.
  * @property {Node} child - Endpoint of the link. This node represents the second timestamp tau2.
  * @property {Selection} selection - Selection containing a single <path> element.
  * @property {Scene} scene - Scene containing the link.
  */
class Link {
  /** @param {Selection} linkSelection - Selection containig a single <path> element.
    * @param {Node} parent - First endpoint of the link.
    * @param {Node} child - Second endpoint of the link.
    * @param {Scene} scene - Scene containing the link.
    */
  constructor(linkSelection, parent, child, scene) {
    this.id = parent.id + child.id;
    this.parent = parent;
    this.child = child;
    this.scene = scene;
    
    this.selection = linkSelection
      .classed("link", true)
      .attr("id", this.id)
      .attr("stroke", "hsl(" + parent.color + ", 100%, 50%)")
      .attr("stroke-width", "2")
      .attr("fill", "none");
  }

  /** Modify the DOM element corresponding to this link (stored in `selection`).
      Attribute `d` is modified to fit the child and parent's positions.
    * @param {number} duration - duration of the modification (in ms).
    */
  refreshElement(duration) {
    const p = this.parent.parentAnchor;
    const c = this.child.childAnchor;
    this.selection
      .transition().duration(duration)
      .attr("d", `M ${p.x} ${p.y} C ${p.x} ${c.y}, ${c.x} ${p.y}, ${c.x} ${c.y}`);
  }
}

/* -------------------------------------------------------------------------- */

/** Contains information about the svg element of the visualisation
  * and the objects representing nodes and links.
  * @property {Configuration} config - Contains variables applied to every object in the scene.
  * @property {Object.<string, Node>} nodes - Pairs a `Node` with its identifier as key.
  * @property {Array.<Array.<Node>>} layout - Describe the layout of the scene.
    Each element in layout correspond to a row of nodes.
    These rows are ordered from top to bottom.
  * @property {Object.<string, Link>} links - Pairs a `Link` with its identifier as key.
  * @property {Selection} selection - Selection containing a single <svg> element.
  * @property {number} width - Width of the scene.
  * @property {number} height - Height of the scene.
  */
class Scene {
  /** @param {Selection} svgSelection - Selection containig a single <svg> element.
    * @param {Configuration} config - Contains global variables of the visualisation.
    */
  constructor(svgSelection, config) {
    this.config = config;
    this.nodes = {};
    this.layout = [];
    this.links = {};
    
    this.selection = svgSelection
      .style("border", "solid");
    this.selection.append("g")
      .classed("links", true);
    this.selection.append("g")
      .classed("nodes", true);
        
    this.width = this.config.margin;
    this.height = this.config.margin;
  }
  
  /** Use D3's data join to create and remove nodes and links.
      Then, we compute sizes and positions
      and refresh all elements of the scene.
    * @param {Data} data - Data sent by the reader.
    */
  plot(data) {
    this.joinNodes(data);
    this.joinLinks(data);
    this.createLayout(data);
    this.updateAllSizesAndPositions();
    this.refreshElement(0);
  }
  
  /** Joins the list of nodes in `data`
      with the list of elements <g> of class `node`.
      For each datum in the `enter` selection, we create a new Node
      and add it to the dictionary `nodes`.
      Each element in the `exit` selection is removed from the dom
      and from `nodes`.
    * @param {Data} data - Data sent by the reader.
    */
  joinNodes(data) {
    this.selection.select("g.nodes").selectAll("g.node")
      .data(data.nodes, d => d.id)
      .join(
        enter => {
          const result = enter.append("g")
          result.each((d,i,nodes) => {
            const selection = d3.select(nodes[i]);
            this.nodes[d.id] = new Node(selection, d, this);
          });
          return result;
        },
        update => {
          return update
        },
        exit => {
          exit.each(d => {
            delete this.nodes[d.id];
          });
          return exit.remove()
        }
      );
  }

  /** Joins the list `data.list` with the list of elements <path>.
      For each datum in the `enter` selection, we add a new Link in `links`.
      Elements in the `exit` selection are removed from the DOM and `links`.
    * @param {Data} data - Data sent by the reader.
    */
  joinLinks(data) {
    const dataLinks = data.nodes.flatMap(parent => {
      return parent.children.map(childId => {
        const child = this.nodes[childId];
        return {"id": parent.id + child.id, "parent": parent, "child": child}
      })
    });
    this.selection.select("g.links").selectAll("path")
      .data(dataLinks, d => d.id)
      .join(
        enter => {
          const result = enter.append("path")
          result.each((d,i,nodes) => {
            const selection = d3.select(nodes[i]);
            const parent = this.nodes[d.parent.id];
            const child = this.nodes[d.child.id];
            this.links[d.id] = (new Link(selection, parent, child, this));
          });
          return result;
        },
        update => update,
        exit => {
          exit.each(d => {
            delete this.links[d.id];
          });
          return exit.remove()
        }
      );
  }
  
  /** Set `layout` equal to `data.layout`
      but with idifiers mapped to their associated Node.
    * @param {Data} data - Data sent by the reader.
    */
  createLayout(data) {
    this.layout = data.layout.map(row => row.map(nodeId => this.nodes[nodeId]));
  }
  
  /** Set the properties `x`, `y`, `width` and `height` in each node.
      Compute `height` and `width` of the scene.
    */
  updateAllSizesAndPositions() {
    let maxX = this.config.margin;
    let y = this.config.margin;
    this.layout.forEach(row => {
      let x = this.config.margin;
      let rowHeight = 0;
      row.forEach(node => {
        node.updateAllSizes();
        node.setPosition(x, y);
        x += node.width + this.config.margin;
        rowHeight = Math.max(rowHeight, node.height);
      });
      maxX = Math.max(maxX, x);
      y += rowHeight + this.config.margin;
    });
    this.width = maxX;
    this.height = y;
  }

  /** Modify the DOM element corresponding to this svg (stored in `selection`).
      Resize the svg and modify each node and link to fit its size and position.
    * @param {number} duration - duration of the modification (in ms).
    */
  refreshElement(duration) {
    this.layout.flat().forEach(node => node.refreshElement(duration));
    for (const id in this.links) {
      this.links[id].refreshElement(duration);
    }
    this.selection
      .transition().duration(duration)
      .attr("width", this.width)
      .attr("height", this.height);
  }
}

/* -------------------------------------------------------------------------- */

/** Handles communication with the local server.
  * Prints the status of the visualisation in a title.
  * Creates or update the scene, if there is one.
  * @property {Configuration} config - Contains global variables of the visualisation.
  * @property {Selection} titleSelection - Selection containing the title. Used to print the status of the visualisation.
  * @property {?Scene} scene - Contains the scene, the object link to the svg, if there is one. Else, its value is `null`.
  * @property {Reader} reader - Reader used to read the data on the local server.
  * @property {EventSource} es - Listens to events sent by the local server.
  */
class Visualisation {
  /** @param {Configuration} config - Contains global variables of the visualisation.
    */
  constructor(config) {
    this.config = config;
    this.titleSelection = d3.select("body")
      .append("h1");
    this.scene = null;

    this.reader = new Reader(config.address);
    this.importData();
    
    this.es = new EventSource("events");
    this.es.addEventListener("update", event => this.importData());
  }
  
  /** Get data from the reader.
    * Update content of the title and the scene accordingly.
    */
  importData() {
    const data = this.reader.data;
    if (data.error) {
      this.titleSelection.html(data.error);
      this.deleteScene(this.config);
    } else {
      this.titleSelection.html("Visualisation");
      this.plotScene(data);
    }
  }

  /** Create a new scene if there is none.
    * Use the scene to plot `data`.
    * @param {Data} data - Data sent by the reader.
    */
  plotScene(data) {
    if (!this.scene) {
      const svgSelection = d3.select("body").append("svg");
      this.scene = new Scene(svgSelection, config);
    }
    this.scene.plot(data);
  }

  /** Remove the scene if there is one
    */
  deleteScene() {
    if (this.scene) {
      this.scene.selection.remove();
      this.scene = null;
    }
  }
}

/* -------------------------------------------------------------------------- */

const config = new Configuration("http://localhost:8080/dump.json", 20, 5, "80em", 200);
const visu = new Visualisation(config);
