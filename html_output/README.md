# Main

## Prerequisite

The Html mode need **pandoc** to run.  
You can find this tool [here](https://pandoc.org/).

## Input

To create a example in a html file, you need:

* A **squirrel file** `PATH1/squirrel_name.sp`
* A **html file** `PATH2/page.html` containing the line:  
`<!--HERE-->` (without spaces or tabulations)

## Command

`./squirrel PATH1/squirrel_name.sp --html PATH2/page.html`

## Output

This command will create a copy of `page.html` in the same directory pointed by `PATH1` named `squirrel_name.html`.

This new file will have the output of squirrel formatted in html and placed where the `<!--HERE-->` tag is.



# The result

Squirrel will put its results between span tags that will not be displayed. This result can later be processed, by a js script for example.

Each instruction in the Squirrel file create the following item :

```
<span class="squirrel-step" id="step_i">
  <span class="input-line" id="in_i">
    Input
  </span>
  <span class="output-line" id="out_i">
    Output
  </span>
  <span class="com-line" id="com_i">
    Comment
  </span>
</span>
```

The `_i` in the tags' id is replaced by the number of the instuctions.

## Input lines

This will be a copy of the instruction of the Squirrel file.

## Output lines

This will be the output given by Squirrel formatted in html.

## Comments

The Squirrel file can contain comments that will be written in Markdown. They will be translated into html by pandoc.

These comments must start with `(**` and end with `*)`.

### Pandoc's Markdown

The Markdown used by pandoc is detailled [here](https://pandoc.org/MANUAL.html#pandocs-markdown).
