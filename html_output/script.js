input_lines = document.querySelectorAll("span.input-line");
output_lines = document.querySelectorAll("span.output-line");
in_line = document.getElementById("in-line");
out_line = document.getElementById("out-line");
prec_line = document.getElementById("prec-line");
selected = null;
i = 0;
n = output_lines.length;
for (j = 0; j < n; j++) {
  line = input_lines[j];
  in_line.appendChild(line);
  line.addEventListener("click", function() { select_line(this);} );
  line.style.color = "black";
  line.number = j;
}

function goto_line(j) {
  if (0 <= j && j <= n){
    if (j <= 1){
      prec_line.innerHTML = ""; 
    } else {
      prec_line.innerHTML = output_lines[j-2].innerHTML;
    }
    if (j == 0){
      out_line.innerHTML = ""; 
    } else {
      out_line.innerHTML = output_lines[j-1].innerHTML;
    }
    for (k = 0; k < j; k++) {
      input_lines[k].style.background = "#50D030";
    }
    for (k = j; k < n; k++) {
      input_lines[k].style.background = "none";
    }
    i = j;
    if (selected != null) {
      selected.style.color = "black";
    }
  }
}

function goto_up() {
  goto_line(i+1)
}

function goto_down() {
  goto_line(i-1)
}

function select_line(obj) {
  if (selected == obj) {
    selected.style.color = "black";
    selected = null
  } else {
    if (selected != null) {
      selected.style.color = "black";
    }
    obj.style.color = "red";
    selected = obj
  }
}

function goto_selected() {
  if (selected != null) {
    goto_line(selected.number + 1);
  }
}
