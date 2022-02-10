# Main

## Prerequisite

The HTML mode needs **pandoc** to run.
You can find this tool [here](https://pandoc.org/).

## Input

To convert a Squirrel development to HTML, you need:

* A **Squirrel file** `PATH1/squirrel_name.sp`
* An **HTML template file** `PATH2/page.html` containing the line:
`<!--HERE-->` (without spaces or tabulations)

A default HTML template can be found at `html_output/page.html`.

## Command

`./squirrel PATH1/squirrel_name.sp --html PATH2/page.html`

## Output

This command will create a copy of `page.html` in the same directory pointed
by `PATH1` named `squirrel_name.html`. **Beware** that, if a file already
exists with this name, it will be deleted by this operation.

This new file will have the output of Squirrel formatted in HTML and placed
where the `<!--HERE-->` tag is.



# The result

Squirrel will put its results between span tags that will not be displayed. This result can later be processed, by a js script for example.

Each instruction in the Squirrel file is translated into an item
of the following form:

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

This will be the output given by Squirrel formatted in HTML.

## Comments

The Squirrel file can contain comments that will be written in Markdown. They will be translated into HTML by pandoc.

These comments must start with `(**` and end with `*)`.

### Pandoc's Markdown

The Markdown used by pandoc is detailled [here](https://pandoc.org/MANUAL.html#pandocs-markdown).
