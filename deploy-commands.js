require('dotenv').config();

const { REST, Routes } = require('discord.js');
const fs = require('fs');

const commands = [];

// Deployment of command files is optional in this setup. If the
// `commands` folder does not exist (migrated into `index.js`), skip
// deployment to avoid ENOENT crashes on platforms like Railway.
const commandsDir = require('path').join(__dirname, 'commands');
if (!fs.existsSync(commandsDir)) {
  console.log('No commands folder found; skipping command deployment.');
  process.exit(0);
}

// If you later add a `commands` folder with command modules, you can
// re-enable reading and pushing them into `commands` here.

const rest = new REST({ version: '10' })
  .setToken(process.env.TOKEN);

(async () => {
  try {
    console.log('جاري تسجيل الأوامر...');

    await rest.put(
      Routes.applicationGuildCommands(
        process.env.CLIENT_ID,
        process.env.GUILD_ID
      ),
      { body: commands }
    );

    console.log('تم تسجيل الأوامر بنجاح ✅');
  } catch (error) {
    console.error(error);
  }
})();