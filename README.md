# math301spring2025
Repository for Math 301 at Vassar College in the Spring 2025 semester.

## Local installation

Lean requires substantial computing power and space to run smoothly. If your computer has enough power and space, follow these instructions to install Lean locally on your computer. Otherwise I recommend [working in the cloud](#cloud-setup).
First you need to install Visual Studio Code and the Lean 4 extension. Instructions for doing that are [here](https://leanprover-community.github.io/get_started.html#regular-install).

Then it's just a matter of installing this repository onto your computer. There are two ways to do this.

### Local installation via point-and-click

The most painless way to install the repository is using VS Code directly. With Lean installed, open any file on your system in VS Code, and then click on the upside-down A

![an upside-down A](figures/lean_symbol.png?raw=true "An upside-down A")

and select `Open Project` -> `Project: Download Project`. Type in the following URL into the text box which appeared:

```
https://github.com/tghyde/math301spring2025.git
```

and then select the directory where you want the project installed, type in the name of a folder (for math301spring2025) and then wait for a minute or two while everything downloads and compiles. Then accept the suggestion to open the course directory, and you should be up and running. Open up VS Code's file explorer (top left of screen)

![File explorer](figures/file_explorer.png?raw=true "File explorer")

 and navigate to the `Math301spring2025` directory, where you should find a folder called `Section 1 Logic` which is where you should get started.

## Cloud setup
Working in the cloud is quick and easy. Follow these steps:
1. Create or log in to your [GitHub account](https://github.com/).
2. Cmd + click the following button to create a GitHub Codespace in a new tab. This may take several minutes for the initial setup.
<a href='https://codespaces.new/tghyde/math301spring2025' target="_blank"><img src='https://github.com/codespaces/badge.svg' style='max-width: 100%;'></a>
3. Codespaces give you an online space in which to work with Lean. **You only need to create the codespace once!** In the future, just go to this link to access your codespace:
[https://github.com/codespaces/](https://github.com/codespaces/)

Keep in mind that the free tier of Codespaces has limits on monthly usage. I think it should be fine for our class, but if not let me know and we'll work something out.



---
Original Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Modified Copyright (c) 2025 Trevor Hyde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

